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

private def mkSmtAppSpineRev (head : SmtTerm) : List SmtTerm -> SmtTerm
  | [] => head
  | x :: xs => SmtTerm.Apply (mkSmtAppSpineRev head xs) x

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

private theorem congTrueSpine_uop1_eq
    (M : SmtModel) (op : UserOp1) (idx rhs : Term) :
    CongTrueSpine M (Term.UOp1 op idx) rhs ->
    rhs = Term.UOp1 op idx := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop1_eq
    (op : UserOp1) (idx rhs : Term) :
    CongTypeSpine (Term.UOp1 op idx) rhs ->
    rhs = Term.UOp1 op idx := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_uop2_eq
    (M : SmtModel) (op : UserOp2) (idx₁ idx₂ rhs : Term) :
    CongTrueSpine M (Term.UOp2 op idx₁ idx₂) rhs ->
    rhs = Term.UOp2 op idx₁ idx₂ := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop2_eq
    (op : UserOp2) (idx₁ idx₂ rhs : Term) :
    CongTypeSpine (Term.UOp2 op idx₁ idx₂) rhs ->
    rhs = Term.UOp2 op idx₁ idx₂ := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_dt_sel_eq
    (M : SmtModel) (s : native_String) (d : Datatype)
    (i j : native_Nat) (rhs : Term) :
    CongTrueSpine M (Term.DtSel s d i j) rhs ->
    rhs = Term.DtSel s d i j := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_dt_sel_eq
    (s : native_String) (d : Datatype) (i j : native_Nat) (rhs : Term) :
    CongTypeSpine (Term.DtSel s d i j) rhs ->
    rhs = Term.DtSel s d i j := by
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

private theorem congTrueSpine_indexed_unary_uop_inv
    (M : SmtModel) (op : UserOp1) (idx x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp1 op idx) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp1 op idx) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTrueSpine_uop1_eq M op idx _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_indexed_unary_uop_inv
    (op : UserOp1) (idx x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp1 op idx) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp1 op idx) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop1_eq op idx _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_indexed2_unary_uop_inv
    (M : SmtModel) (op : UserOp2) (idx₁ idx₂ x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp2 op idx₁ idx₂) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp2 op idx₁ idx₂) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTrueSpine_uop2_eq M op idx₁ idx₂ _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_indexed2_unary_uop_inv
    (op : UserOp2) (idx₁ idx₂ x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp2 op idx₁ idx₂) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp2 op idx₁ idx₂) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop2_eq op idx₁ idx₂ _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_dt_sel_inv
    (M : SmtModel) (s : native_String) (d : Datatype)
    (i j : native_Nat) (x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.DtSel s d i j) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.DtSel s d i j) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTrueSpine_dt_sel_eq M s d i j _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_dt_sel_inv
    (s : native_String) (d : Datatype) (i j : native_Nat) (x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.DtSel s d i j) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.DtSel s d i j) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_dt_sel_eq s d i j _ hHead
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

private theorem smtx_model_eval_eq_false_of_not_smt_value_rel
    (a b : SmtValue) :
    ¬ RuleProofs.smt_value_rel a b ->
    __smtx_model_eval_eq a b = SmtValue.Boolean false := by
  intro h
  cases hEq : __smtx_model_eval_eq a b with
  | Boolean q =>
      cases q with
      | false => rfl
      | true =>
          exact False.elim (h hEq)
  | NotValue =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Numeral _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Rational _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Binary _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Map _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Fun _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Set _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Seq _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Char _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | UValue _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | RegLan _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | DtCons _ _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Apply _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq

private theorem smtx_model_eval_eq_boolean
    (a b : SmtValue) :
    ∃ q, __smtx_model_eval_eq a b = SmtValue.Boolean q := by
  cases a <;> cases b <;> simp [__smtx_model_eval_eq]

private theorem cong_smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
          hNone, hEq])

private theorem cong_smt_type_ne_set_self
    (T : SmtType) :
    T ≠ SmtType.Set T := by
  cases T <;> intro h <;> cases h

private theorem cong_smt_type_ne_guard_wf_set_self
    {T : SmtType}
    (hT : T ≠ SmtType.None) :
    T ≠ __smtx_typeof_guard_wf T (SmtType.Set T) := by
  intro h
  by_cases hWf : __smtx_type_wf T = true
  · have hSet : T = SmtType.Set T := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
    exact cong_smt_type_ne_set_self T hSet
  · have hNone : T = SmtType.None := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
    exact hT hNone

private theorem cong_smt_type_ne_guard_wf_set_full_self
    {T : SmtType}
    (hT : T ≠ SmtType.None) :
    T ≠ __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) := by
  intro h
  by_cases hWf : __smtx_type_wf (SmtType.Set T) = true
  · have hSet : T = SmtType.Set T := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
    exact cong_smt_type_ne_set_self T hSet
  · have hNone : T = SmtType.None := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
    exact hT hNone

private theorem smt_eval_seq_of_smt_type_seq
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm)
    (T : SmtType) :
    __smtx_typeof t = SmtType.Seq T ->
    ∃ s, __smtx_model_eval M t = SmtValue.Seq s := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Seq T := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical hValTy

private theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

private theorem smt_eval_int_of_smt_type_int
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    ∃ n, __smtx_model_eval M t = SmtValue.Numeral n := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Int := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact int_value_canonical hValTy

private theorem native_re_mk_union_self (r : native_RegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union]

private theorem native_re_mk_inter_self (r : native_RegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter]

private def native_list_in_re (xs : List Char) (r : native_RegLan) :
    native_Bool :=
  native_re_nullable <| xs.foldl (fun acc c => native_re_deriv c acc) r

private theorem native_list_in_re_empty :
    (xs : List Char) -> native_list_in_re xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact native_list_in_re_empty xs

private theorem native_re_mk_union_eq_union_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_nullable_mk_union (r s : native_RegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_list_in_re_mk_union :
    (xs : List Char) -> (r s : native_RegLan) ->
      native_list_in_re xs (native_re_mk_union r s) =
        (native_list_in_re xs r || native_list_in_re xs s)
  | [], r, s => by
      simp [native_list_in_re, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, native_list_in_re_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, native_list_in_re_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [native_list_in_re]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [native_list_in_re, native_re_deriv]
            exact native_list_in_re_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_nullable_mk_concat (r s : native_RegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_nullable]

private theorem native_list_in_re_mk_concat_empty_left
    (xs : List Char) (r : native_RegLan) :
    native_list_in_re xs (native_re_mk_concat SmtRegLan.empty r) = false := by
  simp [native_re_mk_concat, native_list_in_re_empty]

private theorem native_list_in_re_mk_concat_empty_right
    (xs : List Char) (r : native_RegLan) :
    native_list_in_re xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, native_list_in_re_empty]

private theorem native_list_in_re_mk_concat_epsilon_left
    (xs : List Char) (r : native_RegLan) :
    native_list_in_re xs (native_re_mk_concat SmtRegLan.epsilon r) =
      native_list_in_re xs r := by
  cases r <;> simp [native_re_mk_concat, native_list_in_re_empty]

private theorem native_list_in_re_mk_concat_epsilon_right
    (xs : List Char) (r : native_RegLan) :
    native_list_in_re xs (native_re_mk_concat r SmtRegLan.epsilon) =
      native_list_in_re xs r := by
  cases r <;> simp [native_re_mk_concat, native_list_in_re_empty]

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

private theorem native_list_in_re_deriv_mk_concat
    (xs : List Char) (c : Char) (r s : native_RegLan) :
    native_list_in_re xs (native_re_deriv c (native_re_mk_concat r s)) =
      native_list_in_re xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_deriv, native_re_nullable,
      native_list_in_re_mk_union, native_list_in_re_empty]
  · by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          native_list_in_re xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_deriv, native_list_in_re_empty]
      rw [hL]
      rw [native_list_in_re_mk_union]
      rw [native_list_in_re_mk_concat_empty_right]
      simp [native_re_deriv, native_list_in_re_empty]
    · by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_deriv, native_re_nullable,
          native_list_in_re_mk_union, native_list_in_re_empty]
      · by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;> simp [native_re_mk_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [native_list_in_re_mk_union]
          rw [native_list_in_re_mk_concat_epsilon_right]
          simp [native_re_deriv, native_list_in_re_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne r s hrEmpty hsEmpty hrEps hsEps
          rw [hMk]
          simp [native_re_deriv, native_list_in_re_mk_union]

private def native_list_in_re_concat :
    List Char -> native_RegLan -> native_RegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && native_list_in_re (c :: cs) s) ||
        native_list_in_re_concat cs (native_re_deriv c r) s

private theorem native_list_in_re_mk_concat :
    (xs : List Char) -> (r s : native_RegLan) ->
      native_list_in_re xs (native_re_mk_concat r s) =
        native_list_in_re_concat xs r s
  | [], r, s => by
      simp [native_list_in_re, native_list_in_re_concat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        native_list_in_re cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              native_list_in_re cs (native_re_deriv c s)) ||
            native_list_in_re_concat cs (native_re_deriv c r) s)
      rw [native_list_in_re_deriv_mk_concat cs c r s]
      rw [native_list_in_re_mk_union]
      rw [native_list_in_re_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [hNullable, native_list_in_re_empty, Bool.or_comm]

private theorem native_list_in_re_concat_true_iff_exists_append :
    (xs : List Char) -> (r s : native_RegLan) ->
      native_list_in_re_concat xs r s = true ↔
        ∃ xs₁ xs₂ : List Char,
          xs₁ ++ xs₂ = xs ∧
            native_list_in_re xs₁ r = true ∧
            native_list_in_re xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        simp [native_list_in_re_concat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [native_list_in_re] using h.1,
          by simpa [native_list_in_re] using h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [native_list_in_re_concat, native_list_in_re] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [native_list_in_re_concat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [native_list_in_re] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (native_list_in_re_concat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [native_list_in_re] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [native_list_in_re] using hLeft
                simp [native_list_in_re_concat, Bool.or_eq_true,
                  Bool.and_eq_true, hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                native_list_in_re ds (native_re_deriv c r) = true := by
              simpa [native_list_in_re] using hLeft
            have hTail :
                native_list_in_re_concat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (native_list_in_re_concat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [native_list_in_re_concat, Bool.or_eq_true, hTail]

private theorem native_list_in_re_mk_concat_true_iff_exists_append
    (xs : List Char) (r s : native_RegLan) :
    native_list_in_re xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List Char,
        xs₁ ++ xs₂ = xs ∧
          native_list_in_re xs₁ r = true ∧
          native_list_in_re xs₂ s = true := by
  rw [native_list_in_re_mk_concat xs r s]
  exact native_list_in_re_concat_true_iff_exists_append xs r s

private theorem native_list_in_re_mk_concat_congr
    (xs : List Char) (r r' s s' : native_RegLan)
    (hr : ∀ ys : List Char, native_list_in_re ys r = native_list_in_re ys r')
    (hs : ∀ ys : List Char, native_list_in_re ys s = native_list_in_re ys s') :
    native_list_in_re xs (native_re_mk_concat r s) =
      native_list_in_re xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (native_list_in_re_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (native_list_in_re_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [← hr xs₁]
    · rwa [← hs xs₂]
  · intro h
    rcases
      (native_list_in_re_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (native_list_in_re_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [hr xs₁]
    · rwa [hs xs₂]

private theorem native_re_nullable_mk_inter (r s : native_RegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_list_in_re_mk_inter :
    (xs : List Char) -> (r s : native_RegLan) ->
      native_list_in_re xs (native_re_mk_inter r s) =
        (native_list_in_re xs r && native_list_in_re xs s)
  | [], r, s => by
      simp [native_list_in_re, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, native_list_in_re_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, native_list_in_re_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [native_list_in_re]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [native_list_in_re, native_re_deriv]
            exact native_list_in_re_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  simpa [native_str_in_re, native_list_in_re] using
    native_list_in_re_mk_union str.toList r s

private theorem native_str_in_re_mk_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  simpa [native_str_in_re, native_list_in_re] using
    native_list_in_re_mk_inter str.toList r s

private theorem native_str_in_re_mk_comp_list :
    ∀ (xs : List Char) (r : native_RegLan),
      native_re_nullable
          (xs.foldl (fun acc c => native_re_deriv c acc)
            (native_re_mk_comp r)) =
        Bool.not
          (native_re_nullable
            (xs.foldl (fun acc c => native_re_deriv c acc) r))
  | [], r => by
      cases r <;> simp [native_re_mk_comp, native_re_nullable]
  | c :: cs, r => by
      have h := native_str_in_re_mk_comp_list cs (native_re_deriv c r)
      cases r <;> simp [native_re_mk_comp, native_re_deriv] at h ⊢
      case comp r =>
        have hComp := native_str_in_re_mk_comp_list cs (native_re_deriv c r)
        have hComp' :
            native_re_nullable
                (List.foldl (fun acc c => native_re_deriv c acc)
                  (match native_re_deriv c r with
                  | SmtRegLan.comp r => r
                  | r => SmtRegLan.comp r)
                  cs) =
              Bool.not
                (native_re_nullable
                    (List.foldl (fun acc c => native_re_deriv c acc)
                      (native_re_deriv c r) cs)) := by
          simpa [native_re_mk_comp] using hComp
        cases hA :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (native_re_deriv c r) cs) <;>
          cases hB :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (match native_re_deriv c r with
                | SmtRegLan.comp r => r
                | r => SmtRegLan.comp r)
                cs) <;>
          simp [hA, hB] at hComp' ⊢ <;> assumption
      all_goals exact h

private theorem native_str_in_re_re_comp
    (s : native_String) (r : native_RegLan) :
    native_str_in_re s (native_re_comp r) =
      Bool.not (native_str_in_re s r) := by
  simpa [native_str_in_re, native_re_comp] using
    native_str_in_re_mk_comp_list s.toList r

private theorem native_str_in_re_re_union
    (s : native_String) (r₁ r₂ : native_RegLan) :
    native_str_in_re s (native_re_union r₁ r₂) =
      (native_str_in_re s r₁ || native_str_in_re s r₂) := by
  simp [native_re_union, native_str_in_re_mk_union]

private theorem native_str_in_re_re_concat_congr
    (s : native_String) (r₁ r₁' r₂ r₂' : native_RegLan)
    (h₁ : ∀ str, native_str_in_re str r₁ = native_str_in_re str r₁')
    (h₂ : ∀ str, native_str_in_re str r₂ = native_str_in_re str r₂') :
    native_str_in_re s (native_re_concat r₁ r₂) =
      native_str_in_re s (native_re_concat r₁' r₂') := by
  have h₁List :
      ∀ ys : List Char, native_list_in_re ys r₁ = native_list_in_re ys r₁' := by
    intro ys
    simpa [native_str_in_re, native_list_in_re] using h₁ (String.ofList ys)
  have h₂List :
      ∀ ys : List Char, native_list_in_re ys r₂ = native_list_in_re ys r₂' := by
    intro ys
    simpa [native_str_in_re, native_list_in_re] using h₂ (String.ofList ys)
  simpa [native_str_in_re, native_list_in_re, native_re_concat] using
    native_list_in_re_mk_concat_congr s.toList r₁ r₁' r₂ r₂' h₁List h₂List

private theorem native_str_in_re_re_inter
    (s : native_String) (r₁ r₂ : native_RegLan) :
    native_str_in_re s (native_re_inter r₁ r₂) =
      (native_str_in_re s r₁ && native_str_in_re s r₂) := by
  simp [native_re_inter, native_str_in_re_mk_inter]

private theorem native_str_in_re_re_diff
    (s : native_String) (r₁ r₂ : native_RegLan) :
    native_str_in_re s (native_re_diff r₁ r₂) =
      (native_str_in_re s r₁ && Bool.not (native_str_in_re s r₂)) := by
  have hComp :
      native_str_in_re s (native_re_mk_comp r₂) =
        Bool.not (native_str_in_re s r₂) := by
    simpa [native_re_comp] using native_str_in_re_re_comp s r₂
  simp [native_re_diff, native_str_in_re_mk_inter, hComp]

private theorem native_list_in_re_deriv_congr
    (c : Char) (r r' : native_RegLan)
    (hExt :
      ∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') :
    ∀ ys : List Char,
      native_list_in_re ys (native_re_deriv c r) =
        native_list_in_re ys (native_re_deriv c r') := by
  intro ys
  simpa [native_list_in_re] using hExt (c :: ys)

private theorem native_re_prefix_match_len_go_congr :
    ∀ (xs : List Char) (r r' : native_RegLan) (n : Nat),
      (∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') ->
      native_re_prefix_match_len?.go r xs n =
        native_re_prefix_match_len?.go r' xs n := by
  intro xs
  induction xs with
  | nil =>
      intro r r' n hExt
      have hNull : native_re_nullable r = native_re_nullable r' := by
        simpa [native_list_in_re] using hExt []
      simp [native_re_prefix_match_len?.go, hNull]
  | cons c cs ih =>
      intro r r' n hExt
      have hNull : native_re_nullable r = native_re_nullable r' := by
        simpa [native_list_in_re] using hExt []
      by_cases hR : native_re_nullable r = true
      · have hRp : native_re_nullable r' = true := by
          simpa [← hNull] using hR
        simp [native_re_prefix_match_len?.go, hR, hRp]
      · have hRfalse : native_re_nullable r = false := by
          cases hVal : native_re_nullable r with
          | false => rfl
          | true => exact False.elim (hR hVal)
        have hRpfalse : native_re_nullable r' = false := by
          simpa [← hNull] using hRfalse
        simp [native_re_prefix_match_len?.go, hRfalse, hRpfalse]
        exact ih (native_re_deriv c r) (native_re_deriv c r') (n + 1)
          (native_list_in_re_deriv_congr c r r' hExt)

private theorem native_re_prefix_match_len_congr
    (r r' : native_RegLan) (xs : List Char)
    (hExt :
      ∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') :
    native_re_prefix_match_len? r xs =
      native_re_prefix_match_len? r' xs := by
  unfold native_re_prefix_match_len?
  exact native_re_prefix_match_len_go_congr xs r r' 0 hExt

private theorem native_re_find_idx_aux_congr :
    ∀ (xs : List Char) (idx : Nat) (r r' : native_RegLan),
      (∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') ->
      native_re_find_idx_aux r xs idx =
        native_re_find_idx_aux r' xs idx := by
  intro xs
  induction xs with
  | nil =>
      intro idx r r' hExt
      have hPref := native_re_prefix_match_len_congr r r' [] hExt
      rw [native_re_find_idx_aux, native_re_find_idx_aux, hPref]
  | cons c cs ih =>
      intro idx r r' hExt
      have hPref := native_re_prefix_match_len_congr r r' (c :: cs) hExt
      rw [native_re_find_idx_aux, native_re_find_idx_aux, hPref]
      cases native_re_prefix_match_len? r' (c :: cs) with
      | none => exact ih (idx + 1) r r' hExt
      | some _ => rfl

private theorem native_re_find_idx_from_congr
    (r r' : native_RegLan) (xs : List Char) (start : Nat)
    (hExt :
      ∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') :
    native_re_find_idx_from r xs start =
      native_re_find_idx_from r' xs start := by
  simp [native_re_find_idx_from,
    native_re_find_idx_aux_congr (xs.drop start) start r r' hExt]

private theorem native_re_find_nonempty_idx_aux_congr :
    ∀ (xs : List Char) (idx : Nat) (r r' : native_RegLan),
      (∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') ->
      native_re_find_nonempty_idx_aux r xs idx =
        native_re_find_nonempty_idx_aux r' xs idx := by
  intro xs
  induction xs with
  | nil =>
      intro idx r r' hExt
      have hPref := native_re_prefix_match_len_congr r r' [] hExt
      rw [native_re_find_nonempty_idx_aux, native_re_find_nonempty_idx_aux,
        hPref]
  | cons c cs ih =>
      intro idx r r' hExt
      have hPref := native_re_prefix_match_len_congr r r' (c :: cs) hExt
      rw [native_re_find_nonempty_idx_aux, native_re_find_nonempty_idx_aux,
        hPref]
      cases native_re_prefix_match_len? r' (c :: cs) with
      | none => exact ih (idx + 1) r r' hExt
      | some n =>
          cases n with
          | zero => exact ih (idx + 1) r r' hExt
          | succ _ => rfl

private theorem native_re_find_nonempty_idx_from_congr
    (r r' : native_RegLan) (xs : List Char) (start : Nat)
    (hExt :
      ∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') :
    native_re_find_nonempty_idx_from r xs start =
      native_re_find_nonempty_idx_from r' xs start := by
  simp [native_re_find_nonempty_idx_from,
    native_re_find_nonempty_idx_aux_congr (xs.drop start) start r r' hExt]

private theorem native_re_replace_all_nonempty_list_aux_congr :
    ∀ (fuel : Nat) (xs replacement : List Char) (r r' : native_RegLan),
      (∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') ->
      native_re_replace_all_nonempty_list_aux fuel r replacement xs =
        native_re_replace_all_nonempty_list_aux fuel r' replacement xs := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs replacement r r' hExt
      rfl
  | succ fuel ih =>
      intro xs replacement r r' hExt
      cases xs with
      | nil =>
          have hPref := native_re_prefix_match_len_congr r r' [] hExt
          rw [native_re_replace_all_nonempty_list_aux.eq_2,
            native_re_replace_all_nonempty_list_aux.eq_2, hPref]
          cases native_re_prefix_match_len? r' [] with
          | none => rfl
          | some n =>
              cases n with
              | zero => rfl
              | succ n =>
                  simp
                  exact ih [] replacement r r' hExt
      | cons c cs =>
          have hPref := native_re_prefix_match_len_congr r r' (c :: cs) hExt
          rw [native_re_replace_all_nonempty_list_aux.eq_3,
            native_re_replace_all_nonempty_list_aux.eq_3, hPref]
          cases native_re_prefix_match_len? r' (c :: cs) with
          | none =>
              rw [ih cs replacement r r' hExt]
          | some n =>
              cases n with
              | zero =>
                  rw [ih cs replacement r r' hExt]
              | succ n =>
                  simp
                  exact ih (List.drop n cs) replacement r r' hExt

private theorem native_re_replace_all_nonempty_list_congr
    (r r' : native_RegLan) (replacement xs : List Char)
    (hExt :
      ∀ ys : List Char,
        native_list_in_re ys r = native_list_in_re ys r') :
    native_re_replace_all_nonempty_list r replacement xs =
      native_re_replace_all_nonempty_list r' replacement xs := by
  exact native_re_replace_all_nonempty_list_aux_congr
    (xs.length + 1) xs replacement r r' hExt

private theorem native_str_ext_to_list_ext
    (r r' : native_RegLan)
    (hExt :
      ∀ str : native_String,
        native_str_in_re str r = native_str_in_re str r') :
    ∀ ys : List Char,
      native_list_in_re ys r = native_list_in_re ys r' := by
  intro ys
  simpa [native_str_in_re, native_list_in_re] using hExt (String.ofList ys)

private theorem native_str_indexof_re_congr
    (s : native_String) (r r' : native_RegLan) (i : native_Int)
    (hExt :
      ∀ str : native_String,
        native_str_in_re str r = native_str_in_re str r') :
    native_str_indexof_re s r i = native_str_indexof_re s r' i := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  by_cases hLt : i < 0
  · simp [native_str_indexof_re, hLt]
  · simp [native_str_indexof_re, hLt,
      native_re_find_idx_from_congr r r' s.toList (Int.toNat i) hExtList]

private theorem native_str_replace_re_congr
    (s : native_String) (r r' : native_RegLan) (replacement : native_String)
    (hExt :
      ∀ str : native_String,
        native_str_in_re str r = native_str_in_re str r') :
    native_str_replace_re s r replacement =
      native_str_replace_re s r' replacement := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  simp [native_str_replace_re,
    native_re_find_nonempty_idx_from_congr r r' s.toList 0 hExtList]

private theorem native_str_replace_re_all_congr
    (s : native_String) (r r' : native_RegLan) (replacement : native_String)
    (hExt :
      ∀ str : native_String,
        native_str_in_re str r = native_str_in_re str r') :
    native_str_replace_re_all s r replacement =
      native_str_replace_re_all s r' replacement := by
  have hExtList := native_str_ext_to_list_ext r r' hExt
  simp [native_str_replace_re_all,
    native_re_replace_all_nonempty_list_congr r r' replacement.toList
      s.toList hExtList]

private theorem smt_value_rel_model_eval_eq_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq a b) (__smtx_model_eval_eq c d) := by
  intro hac hbd
  have hIff :
      RuleProofs.smt_value_rel a b ↔
        RuleProofs.smt_value_rel c d := by
    constructor
    · intro hab
      exact RuleProofs.smt_value_rel_trans c a d
        (RuleProofs.smt_value_rel_symm a c hac)
        (RuleProofs.smt_value_rel_trans a b d hab hbd)
    · intro hcd
      exact RuleProofs.smt_value_rel_trans a c b hac
        (RuleProofs.smt_value_rel_trans c d b hcd
          (RuleProofs.smt_value_rel_symm b d hbd))
  by_cases hab : RuleProofs.smt_value_rel a b
  · have hcd : RuleProofs.smt_value_rel c d := hIff.mp hab
    unfold RuleProofs.smt_value_rel at hab hcd ⊢
    rw [hab, hcd]
    simp [__smtx_model_eval_eq, native_veq]
  · have hncd : ¬ RuleProofs.smt_value_rel c d := by
      intro hcd
      exact hab (hIff.mpr hcd)
    have habFalse :
        __smtx_model_eval_eq a b = SmtValue.Boolean false :=
      smtx_model_eval_eq_false_of_not_smt_value_rel a b hab
    have hcdFalse :
        __smtx_model_eval_eq c d = SmtValue.Boolean false :=
      smtx_model_eval_eq_false_of_not_smt_value_rel c d hncd
    rw [habFalse, hcdFalse]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]

private theorem congTrueSpine_eq_eq_true
    (M : SmtModel) (_hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.eq x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x₁) (__eo_to_smt x₂)))
      (__smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt y₁) (__eo_to_smt y₂)))
    rw [__smtx_model_eval.eq_134, __smtx_model_eval.eq_134]
    exact smt_value_rel_model_eval_eq_congr
      (__smtx_model_eval M (__eo_to_smt x₁))
      (__smtx_model_eval M (__eo_to_smt x₂))
      (__smtx_model_eval M (__eo_to_smt y₁))
      (__smtx_model_eval M (__eo_to_smt y₂))
      (smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁)
      (smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂)

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

private theorem congTrueSpine_non_reg_unop_eq_true_of_eval_congr
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
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
    (hEvalCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
          __smtx_model_eval M a = __smtx_model_eval M b ->
          __smtx_model_eval M (smtOp a) =
            __smtx_model_eval M (smtOp b))
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
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← hArgTy]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    have hOpEval :
        __smtx_model_eval M (smtOp (__eo_to_smt x)) =
          __smtx_model_eval M (smtOp (__eo_to_smt y)) :=
      hEvalCong (__eo_to_smt x) (__eo_to_smt y) hArgTy hEvalArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hOpEval]
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

private theorem congTrueSpine_non_reg_indexed_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp1) (idx : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) a) =
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
      (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp1 eoOp idx) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_unary_uop_inv M eoOp idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp1 eoOp idx) x)
        (Term.Apply (Term.UOp1 eoOp idx) y) hEqBool
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

private theorem congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
    (eoOp : UserOp1) (idx : Term) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp1 eoOp idx) x) ->
    CongTypeSpine (Term.Apply (Term.UOp1 eoOp idx) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 eoOp idx) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed_unary_uop_inv eoOp idx x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 eoOp idx) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp1 eoOp idx) x)
    (Term.Apply (Term.UOp1 eoOp idx) y)
    hOpTy
    hTrans

private theorem congTrueSpine_non_reg_indexed2_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp2) (idx₁ idx₂ : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) a) =
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
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed2_unary_uop_inv M eoOp idx₁ idx₂ x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)
        (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y) hEqBool
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

private theorem congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
    (eoOp : UserOp2) (idx₁ idx₂ : Term)
    (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) ->
    CongTypeSpine (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_indexed2_unary_uop_inv eoOp idx₁ idx₂ x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) x)
    (Term.Apply (Term.UOp2 eoOp idx₁ idx₂) y)
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

private theorem congTypeSpine_eq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.eq SmtTerm.eq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_eq_eq, typeof_eq_eq, ha, hb])
    x₁ x₂ rhs

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

private theorem congTrueSpine_ite_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (c t e rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.ite c t e rhs hSpine with
    ⟨c', t', e', hRhs, hCond, hThen, hElse⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c') t') e')
        hEqBool
    have hLeftNN :
        __smtx_typeof
            (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) ≠
          SmtType.None := by
      simpa using hTypes.2
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)) := by
      unfold term_has_non_none_type
      exact hLeftNN
    rcases ite_args_of_non_none hIteNN with
      ⟨_T, hcBool, _htTy, _heTy, _hTNN⟩
    have hc'Bool :
        __smtx_typeof (__eo_to_smt c') = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M c c' hCond]
      exact hcBool
    have hCondEval :
        __smtx_model_eval M (__eo_to_smt c) =
          __smtx_model_eval M (__eo_to_smt c') :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM c c'
        SmtType.Bool hcBool hc'Bool (by simp) (by simp) hCond
    have hc'NN : term_has_non_none_type (__eo_to_smt c') := by
      unfold term_has_non_none_type
      rw [hc'Bool]
      simp
    have hc'ValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c')) =
          SmtType.Bool := by
      simpa [hc'Bool] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c') hc'NN
    rcases bool_value_canonical hc'ValTy with ⟨b, hc'Val⟩
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e)))
        (__smtx_model_eval M
          (SmtTerm.ite (__eo_to_smt c') (__eo_to_smt t') (__eo_to_smt e')))
    rw [__smtx_model_eval.eq_133, __smtx_model_eval.eq_133]
    rw [hCondEval, hc'Val]
    cases b with
    | false =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M e e' hElse
    | true =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M t t' hThen

private theorem congTypeSpine_ite_eq_has_bool_type
    (c t e rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e)
        rhs) :=
  congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.ite SmtTerm.ite
    (by intro a b c; rfl)
    (by
      intro a b c a' b' c' ha hb hc
      rw [typeof_ite_eq, typeof_ite_eq, ha, hb, hc])
    c t e rhs

private theorem smt_value_rel_model_eval_apply_of_rel_core
    (M : SmtModel) (hM : model_total_typed M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply M (__smtx_model_eval M g) (__smtx_model_eval M y)) := by
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
  have hANeReg : A ≠ SmtType.RegLan :=
    TranslationProofs.smtx_term_fun_like_arg_ne_reglan_of_non_none
      f hFNN hHead
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

private theorem smt_apply_head_non_none_of_apply_non_none
    {f x : SmtTerm}
    (hAppNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, _hX, _hA, _hB⟩
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem mkSmtAppSpineRev_ne_dt_sel
    {F : SmtTerm}
    (hF : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j) :
    ∀ xs s d i j,
      mkSmtAppSpineRev F xs ≠ SmtTerm.DtSel s d i j
  | [], s, d, i, j => hF s d i j
  | _ :: _, _s, _d, _i, _j => by
      intro h
      cases h

private theorem mkSmtAppSpineRev_ne_dt_tester
    {F : SmtTerm}
    (hF : ∀ s d i, F ≠ SmtTerm.DtTester s d i) :
    ∀ xs s d i,
      mkSmtAppSpineRev F xs ≠ SmtTerm.DtTester s d i
  | [], s, d, i => hF s d i
  | _ :: _, _s, _d, _i => by
      intro h
      cases h

private theorem smt_app_spine_type_eq_of_listRel_bool
    {F G : SmtTerm}
    (hFType : __smtx_typeof F = __smtx_typeof G)
    (hFNoSel : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hFNoTester : ∀ s d i, F ≠ SmtTerm.DtTester s d i)
    (hGNoSel : ∀ s d i j, G ≠ SmtTerm.DtSel s d i j)
    (hGNoTester : ∀ s d i, G ≠ SmtTerm.DtTester s d i) :
    ∀ {xs ys : List Term},
      ListRel EqBoolOrSame xs ys ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
          __smtx_typeof (mkSmtAppSpineRev G (ys.map __eo_to_smt))
  | [], [], ListRel.nil => by
      simpa [mkSmtAppSpineRev] using hFType
  | x :: xs, y :: ys, ListRel.cons hArg hTail => by
      have hTailTy :=
        smt_app_spine_type_eq_of_listRel_bool hFType hFNoSel hFNoTester
          hGNoSel hGNoTester hTail
      have hArgTy : __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
        smt_type_eq_of_eq_bool_or_same x y hArg
      let LF := mkSmtAppSpineRev F (xs.map __eo_to_smt)
      let RG := mkSmtAppSpineRev G (ys.map __eo_to_smt)
      have hGenL : generic_apply_type LF (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenR : generic_apply_type RG (__eo_to_smt y) :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      unfold generic_apply_type at hGenL hGenR
      change
        __smtx_typeof (SmtTerm.Apply LF (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Apply RG (__eo_to_smt y))
      rw [hGenL, hGenR]
      simp [LF, RG, hTailTy, hArgTy]

private theorem smt_app_spine_type_eq_and_rel_of_listRel_true
    (M : SmtModel) (hM : model_total_typed M)
    {F G : SmtTerm}
    (hFType : __smtx_typeof F = __smtx_typeof G)
    (hFRel :
      RuleProofs.smt_value_rel (__smtx_model_eval M F)
        (__smtx_model_eval M G))
    (hFNoSel : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hFNoTester : ∀ s d i, F ≠ SmtTerm.DtTester s d i)
    (hGNoSel : ∀ s d i j, G ≠ SmtTerm.DtSel s d i j)
    (hGNoTester : ∀ s d i, G ≠ SmtTerm.DtTester s d i) :
    ∀ {xs ys : List Term},
      ListRel (EqTrueOrSame M) xs ys ->
      __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) ≠
        SmtType.None ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
            __smtx_typeof (mkSmtAppSpineRev G (ys.map __eo_to_smt)) ∧
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (mkSmtAppSpineRev F (xs.map __eo_to_smt)))
            (__smtx_model_eval M
              (mkSmtAppSpineRev G (ys.map __eo_to_smt)))
  | [], [], ListRel.nil => by
      intro _hNN
      exact ⟨by simpa [mkSmtAppSpineRev] using hFType,
        by simpa [mkSmtAppSpineRev] using hFRel⟩
  | x :: xs, y :: ys, ListRel.cons hArg hTail => by
      intro hNN
      let LF := mkSmtAppSpineRev F (xs.map __eo_to_smt)
      let RG := mkSmtAppSpineRev G (ys.map __eo_to_smt)
      let X := __eo_to_smt x
      let Y := __eo_to_smt y
      have hGenTyL : generic_apply_type LF X :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenTyR : generic_apply_type RG Y :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      have hGenEvalL : generic_apply_eval LF X :=
        generic_apply_eval_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenEvalR : generic_apply_eval RG Y :=
        generic_apply_eval_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      unfold generic_apply_type at hGenTyL hGenTyR
      have hAppNN : __smtx_typeof_apply (__smtx_typeof LF) (__smtx_typeof X) ≠
          SmtType.None := by
        rw [← hGenTyL]
        simpa [LF, X, mkSmtAppSpineRev] using hNN
      have hTailNN : __smtx_typeof LF ≠ SmtType.None :=
        smt_apply_head_non_none_of_apply_non_none hAppNN
      have hTail :=
        smt_app_spine_type_eq_and_rel_of_listRel_true M hM hFType hFRel
          hFNoSel hFNoTester hGNoSel hGNoTester hTail hTailNN
      have hTailTy : __smtx_typeof LF = __smtx_typeof RG := by
        simpa [LF, RG] using hTail.1
      have hTailRel :
          RuleProofs.smt_value_rel (__smtx_model_eval M LF)
            (__smtx_model_eval M RG) := by
        simpa [LF, RG] using hTail.2
      have hArgTy : __smtx_typeof X = __smtx_typeof Y := by
        exact smt_type_eq_of_eq_true_or_same M x y hArg
      have hArgRel :
          RuleProofs.smt_value_rel (__smtx_model_eval M X)
            (__smtx_model_eval M Y) := by
        exact smt_value_rel_of_eq_true_or_same M x y hArg
      have hTypeEq :
          __smtx_typeof (SmtTerm.Apply LF X) =
            __smtx_typeof (SmtTerm.Apply RG Y) := by
        rw [hGenTyL, hGenTyR]
        rw [hTailTy, hArgTy]
      have hRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (SmtTerm.Apply LF X))
            (__smtx_model_eval M (SmtTerm.Apply RG Y)) := by
        unfold generic_apply_eval at hGenEvalL hGenEvalR
        rw [hGenEvalL M, hGenEvalR M]
        exact smt_value_rel_model_eval_apply_of_rel_core M hM LF RG X Y
          hAppNN hTailTy hArgTy hTailRel hArgRel
      exact ⟨by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hTypeEq,
        by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hRel⟩

private theorem congTrueSpine_var_apply_inv
    (M : SmtModel) (s : native_String) (T x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.Var (Term.String s) T) y ∧
        EqTrueOrSame M x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_var_apply_inv
    (s : native_String) (T x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.Var (Term.String s) T) y ∧
        EqBoolOrSame x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_uconst_apply_inv
    (M : SmtModel) (i : native_Nat) (T x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UConst i T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.UConst i T) y ∧
        EqTrueOrSame M x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_var_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTrueSpine_var_apply_inv M s T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTrueSpine_uconst_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTrueSpine_uconst_apply_inv M i T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTypeSpine_uconst_apply_inv
    (i : native_Nat) (T x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UConst i T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.UConst i T) y ∧
        EqBoolOrSame x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_var_apply_apply_inv
    (s : native_String) (T x₁ x₂ rhs : Term) :
    CongTypeSpine
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_var_apply_inv s T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTypeSpine_uconst_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    CongTypeSpine (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_uconst_apply_inv i T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTrueSpine_var_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs ->
      ∃ y₁ y₂ y₃,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTrueSpine_var_apply_apply_inv M s T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTrueSpine_uconst_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs ->
      ∃ y₁ y₂ y₃,
        rhs = Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTrueSpine_uconst_apply_apply_inv M i T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTypeSpine_var_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs ->
      ∃ y₁ y₂ y₃,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_var_apply_apply_inv s T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTypeSpine_uconst_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs ->
      ∃ y₁ y₂ y₃,
        rhs = Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_uconst_apply_apply_inv i T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTrueSpine_var_apply_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTrueSpine_var_apply_apply_apply_inv M s T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTrueSpine_uconst_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTrueSpine_uconst_apply_apply_apply_inv M i T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTypeSpine_var_apply_apply_apply_inv s T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTypeSpine_uconst_apply_apply_apply_inv i T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTrueSpine_var_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTrueSpine_var_apply_apply_apply_apply_inv M s T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTrueSpine_uconst_apply_apply_apply_apply_inv M i T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTypeSpine_var_apply_apply_apply_apply_inv s T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTypeSpine_uconst_apply_apply_apply_apply_inv i T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTrueSpine_var_apply_apply_apply_apply_apply_apply_inv
    (M : SmtModel)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ ∧ EqTrueOrSame M x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTrueSpine_var_apply_apply_apply_apply_apply_inv M s T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ ∧ EqTrueOrSame M x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_inv M i T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ ∧ EqBoolOrSame x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTypeSpine_var_apply_apply_apply_apply_apply_inv s T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ ∧ EqBoolOrSame x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_inv i T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTypeSpine_var_apply_eq_has_bool_type
    (s : native_String) (T x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Var (Term.String s) T) x) ->
    CongTypeSpine (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_inv s T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hAppTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y))
    simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Var (Term.String s) T) x)
    (Term.Apply (Term.Var (Term.String s) T) y)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_eq_has_bool_type
    (i : native_Nat) (T x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UConst i T) x) ->
    CongTypeSpine (Term.Apply (Term.UConst i T) x) rhs ->
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UConst i T) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_inv i T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hAppTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt y))
    simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UConst i T) x)
    (Term.Apply (Term.UConst i T) y)
    hAppTy hTrans

private theorem congTypeSpine_var_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_inv s T x₁ x₂ rhs hSpine with
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
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt x₁))
            (__eo_to_smt x₂)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt y₁))
            (__eo_to_smt y₂))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) ->
    CongTypeSpine (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_inv i T x₁ x₂ rhs hSpine with
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
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
              (__eo_to_smt x₁))
            (__eo_to_smt x₂)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
              (__eo_to_smt y₁))
            (__eo_to_smt y₂))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
    hAppTy hTrans

private theorem congTypeSpine_var_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_inv s T x₁ x₂ x₃ rhs hSpine with
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
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt x₁))
              (__eo_to_smt x₂))
            (__eo_to_smt x₃)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt y₁))
              (__eo_to_smt y₂))
            (__eo_to_smt y₃))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂) y₃)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_inv i T x₁ x₂ x₃ rhs
      hSpine with
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
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt x₁))
              (__eo_to_smt x₂))
            (__eo_to_smt x₃)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt y₁))
              (__eo_to_smt y₂))
            (__eo_to_smt y₃))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
    (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃)
    hAppTy hTrans

private theorem congTypeSpine_var_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
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
  have hArgTy₄ :
      __smtx_typeof (__eo_to_smt x₄) =
        __smtx_typeof (__eo_to_smt y₄) :=
    smt_type_eq_of_eq_bool_or_same x₄ y₄ hArg₄
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                  (__eo_to_smt x₁))
                (__eo_to_smt x₂))
              (__eo_to_smt x₃))
            (__eo_to_smt x₄)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                  (__eo_to_smt y₁))
                (__eo_to_smt y₂))
              (__eo_to_smt y₃))
            (__eo_to_smt y₄))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃, hArgTy₄]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) x₄)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
        y₃) y₄)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
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
  have hArgTy₄ :
      __smtx_typeof (__eo_to_smt x₄) =
        __smtx_typeof (__eo_to_smt y₄) :=
    smt_type_eq_of_eq_bool_or_same x₄ y₄ hArg₄
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                  (__eo_to_smt x₁))
                (__eo_to_smt x₂))
              (__eo_to_smt x₃))
            (__eo_to_smt x₄)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                  (__eo_to_smt y₁))
                (__eo_to_smt y₂))
              (__eo_to_smt y₃))
            (__eo_to_smt y₄))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃, hArgTy₄]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
        x₃) x₄)
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
        y₃) y₄)
    hAppTy hTrans

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁)
                    x₂) x₃) x₄) x₅)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁)
                    y₂) y₃) y₄) y₅)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt x₅, __eo_to_smt x₄, __eo_to_smt x₃,
              __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt y₅, __eo_to_smt y₄, __eo_to_smt y₃,
              __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₅
        (ListRel.cons hArg₄
          (ListRel.cons hArg₃
            (ListRel.cons hArg₂
              (ListRel.cons hArg₁ ListRel.nil)))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) x₅)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
          y₃) y₄) y₅)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁)
                  x₂) x₃) x₄) x₅)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁)
                  y₂) y₃) y₄) y₅)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt x₅, __eo_to_smt x₄, __eo_to_smt x₃,
              __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt y₅, __eo_to_smt y₄, __eo_to_smt y₃,
              __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₅
        (ListRel.cons hArg₄
          (ListRel.cons hArg₃
            (ListRel.cons hArg₂
              (ListRel.cons hArg₁ ListRel.nil)))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) x₅)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
          y₃) y₄) y₅)
    hAppTy hTrans

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁)
                      x₂) x₃) x₄) x₅) x₆)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁)
                      y₂) y₃) y₄) y₅) y₆)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt x₆, __eo_to_smt x₅, __eo_to_smt x₄,
              __eo_to_smt x₃, __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt y₆, __eo_to_smt y₅, __eo_to_smt y₄,
              __eo_to_smt y₃, __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₆
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil))))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) x₆)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃) y₄) y₅) y₆)
    hAppTy hTrans

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁)
                    x₂) x₃) x₄) x₅) x₆)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁)
                    y₂) y₃) y₄) y₅) y₆)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt x₆, __eo_to_smt x₅, __eo_to_smt x₄,
              __eo_to_smt x₃, __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt y₆, __eo_to_smt y₅, __eo_to_smt y₄,
              __eo_to_smt y₃, __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₆
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil))))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) x₆)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
            y₃) y₄) y₅) y₆)
    hAppTy hTrans

private theorem congTrueSpine_var_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_inv M s T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Var (Term.String s) T) x)
        (Term.Apply (Term.Var (Term.String s) T) y) hEqBool
    have hLeftNN :
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) ≠
            SmtType.None := by
      simpa using hTypes.2
    have hAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hLeftNN
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hArgRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y)))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
      (SmtTerm.Var s (__eo_to_smt_type T))
      (SmtTerm.Var s (__eo_to_smt_type T))
      (__eo_to_smt x) (__eo_to_smt y)
      hAppNN rfl hArgTy (RuleProofs.smt_value_rel_refl _) hArgRel

private theorem congTrueSpine_uconst_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x rhs : Term) :
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UConst i T) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UConst i T) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UConst i T) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_inv M i T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UConst i T) x)
        (Term.Apply (Term.UConst i T) y) hEqBool
    have hLeftNN :
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)) ≠ SmtType.None := by
      simpa using hTypes.2
    have hAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hLeftNN
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hArgRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt y)))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
      (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
      (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
      (__eo_to_smt x) (__eo_to_smt y)
      hAppNN rfl hArgTy (RuleProofs.smt_value_rel_refl _) hArgRel

private theorem congTrueSpine_var_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_inv M s T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
        hEqBool
    have hOuterLeftNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      simpa [F, X₁, X₂] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hInnerNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [__smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
        hOuterAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂

private theorem congTrueSpine_uconst_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) ->
    CongTrueSpine M (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_inv M i T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) hEqBool
    have hOuterLeftNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      simpa [F, X₁, X₂] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hInnerNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [__smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
        hOuterAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂

private theorem congTrueSpine_var_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_inv M s T x₁ x₂ x₃ rhs
      hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
          y₃) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      simpa [F, X₁, X₂, X₃] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃))
    have hMidNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMidAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMidNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMidAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMidTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMidRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMidAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
        (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
        hOuterAppNN hMidTy hArgTy₃ hMidRel hArgRel₃

private theorem congTrueSpine_uconst_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_inv M i T x₁ x₂ x₃ rhs
      hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃)
        hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      simpa [F, X₁, X₂, X₃] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃))
    have hMidNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMidAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMidNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMidAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMidTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMidRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMidAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
        (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
        hOuterAppNN hMidTy hArgTy₃ hMidRel hArgRel₃

private theorem congTrueSpine_var_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_inv M s T x₁ x₂ x₃ x₄
      rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃) y₄) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
              X₄) ≠ SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
            (__smtx_typeof X₄) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgTy₄ : __smtx_typeof X₄ = __smtx_typeof Y₄ := by
      exact smt_type_eq_of_eq_true_or_same M x₄ y₄ hArg₄
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₄ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₄) (__smtx_model_eval M Y₄) := by
      exact smt_value_rel_of_eq_true_or_same M x₄ y₄ hArg₄
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
            X₄))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
            Y₄))
    have hMid3NN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMid3AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hMid3NN
    have hMid2NN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hMid3AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMid2AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMid2NN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMid2AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMid2Ty :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMid2Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMid2AppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    have hMid3Ty :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) =
          __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃) := by
      simp [__smtx_typeof, hMid2Ty, hArgTy₃]
    have hMid3Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
          (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
          hMid3AppNN hMid2Ty hArgTy₃ hMid2Rel hArgRel₃
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
        X₄ Y₄ hOuterAppNN hMid3Ty hArgTy₄ hMid3Rel hArgRel₄

private theorem congTrueSpine_uconst_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_inv M i T x₁ x₂ x₃
      x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
            y₃) y₄) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
              X₄) ≠ SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄] using hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
            (__smtx_typeof X₄) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgTy₄ : __smtx_typeof X₄ = __smtx_typeof Y₄ := by
      exact smt_type_eq_of_eq_true_or_same M x₄ y₄ hArg₄
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₄ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₄) (__smtx_model_eval M Y₄) := by
      exact smt_value_rel_of_eq_true_or_same M x₄ y₄ hArg₄
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
            X₄))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
            Y₄))
    have hMid3NN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMid3AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hMid3NN
    have hMid2NN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hMid3AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hMid2AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMid2NN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMid2AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMid2Ty :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMid2Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMid2AppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    have hMid3Ty :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) =
          __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃) := by
      simp [__smtx_typeof, hMid2Ty, hArgTy₃]
    have hMid3Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
          (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
          hMid3AppNN hMid2Ty hArgTy₃ hMid2Rel hArgRel₃
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
        X₄ Y₄ hOuterAppNN hMid3Ty hArgTy₄ hMid3Rel hArgRel₄

private theorem congTrueSpine_var_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_apply_inv M s T x₁ x₂ x₃
      x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄) y₅) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]) ≠ SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄, X₅, mkSmtAppSpineRev] using hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M (mkSmtAppSpineRev F [Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil)))))
        hLeftNN).2

private theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_inv M i T x₁ x₂
      x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄) y₅) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]) ≠ SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄, X₅, mkSmtAppSpineRev] using hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M (mkSmtAppSpineRev F [Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil)))))
        hLeftNN).2

private theorem congTrueSpine_var_apply_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_apply_apply_inv M s T
      x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let X₆ : SmtTerm := __eo_to_smt x₆
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    let Y₆ : SmtTerm := __eo_to_smt y₆
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅) y₆) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]) ≠
            SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄, X₅, X₆, mkSmtAppSpineRev] using hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [Y₆, Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₆
          (ListRel.cons hArg₅
            (ListRel.cons hArg₄
              (ListRel.cons hArg₃
                (ListRel.cons hArg₂
                  (ListRel.cons hArg₁ ListRel.nil))))))
        hLeftNN).2

private theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_inv M i T
      x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let X₆ : SmtTerm := __eo_to_smt x₆
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    let Y₆ : SmtTerm := __eo_to_smt y₆
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅) y₆) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]) ≠
            SmtType.None := by
      simpa [F, X₁, X₂, X₃, X₄, X₅, X₆, mkSmtAppSpineRev] using hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [X₆, X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M
          (mkSmtAppSpineRev F [Y₆, Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₆
          (ListRel.cons hArg₅
            (ListRel.cons hArg₄
              (ListRel.cons hArg₃
                (ListRel.cons hArg₂
                  (ListRel.cons hArg₁ ListRel.nil))))))
        hLeftNN).2

private theorem congTypeSpine_bvsize_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_bvsize) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv UserOp._at_bvsize x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)) := by
    let op : SmtTerm -> SmtTerm := fun a =>
      let w := __smtx_bv_sizeof_type (__smtx_typeof a)
      native_ite (native_zleq 0 w)
        (SmtTerm._at_purify (SmtTerm.Numeral w))
        SmtTerm.None
    change
      __smtx_typeof (op (__eo_to_smt x)) =
        __smtx_typeof (op (__eo_to_smt y))
    simp [op, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)
    (Term.Apply (Term.UOp UserOp._at_bvsize) y)
    hOpTy hTrans

private theorem congTrueSpine_bvsize_eq_true
    (M : SmtModel) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_bvsize) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp._at_bvsize x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    let op : SmtTerm -> SmtTerm := fun a =>
      let w := __smtx_bv_sizeof_type (__smtx_typeof a)
      native_ite (native_zleq 0 w)
        (SmtTerm._at_purify (SmtTerm.Numeral w))
        SmtTerm.None
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (op (__eo_to_smt x)))
        (__smtx_model_eval M (op (__eo_to_smt y)))
    have hTerm :
        op (__eo_to_smt x) = op (__eo_to_smt y) := by
      simp [op, hArgTy]
    rw [hTerm]
    exact RuleProofs.smt_value_rel_refl _

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
    (__smtx_model_eval_apply M
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
    (__smtx_model_eval_apply M
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
      (__smtx_model_eval_apply M
        (__smtx_model_lookup M native_div_by_zero_id
          (SmtType.FunType SmtType.Int SmtType.Int))
        _v3)
      (__smtx_model_eval_div_total _v3
        (__smtx_model_eval_multmult_total _v2
          (__smtx_model_eval__ _v1 _v0))))

private noncomputable abbrev smtEvalQdiv
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0
      (SmtValue.Rational (native_mk_rational 0 1)))
    (__smtx_model_eval_apply M
      (__smtx_model_lookup M native_qdiv_by_zero_id
        (SmtType.FunType SmtType.Real SmtType.Real))
      _v1)
    (__smtx_model_eval_qdiv_total _v1 _v0)

private theorem div_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (SmtTerm.div a (SmtTerm.Numeral 0)) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro x y; exact typeof_div_eq x y)
      a (SmtTerm.Numeral 0) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem mod_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (SmtTerm.mod a (SmtTerm.Numeral 0)) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
      (by intro x y; exact typeof_mod_eq x y)
      a (SmtTerm.Numeral 0) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem qdiv_by_zero_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1))) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases arith_overload_ret_binop_args_non_reg_of_non_none
      SmtTerm.qdiv SmtType.Real
      (by intro x y; exact typeof_qdiv_eq x y)
      a (SmtTerm.Rational (native_mk_rational 0 1)) hNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem bv_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_unop_arg_of_non_none (op := op) (hTy a) hTerm with
    ⟨w, hA⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem bv_unop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_unop_ret_arg_of_non_none (op := op) (ret := R)
      (hTy a) hTerm with
    ⟨w, hA⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem extract_arg_non_reg_of_non_none
    (i j a : SmtTerm) :
    __smtx_typeof (SmtTerm.extract i j a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.extract i j a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases extract_args_of_non_none hTerm with
    ⟨_hi, _hj, w, _hI, _hJ, hA, _hj0, _hji, _hiw⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem repeat_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.repeat i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.repeat i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases repeat_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem zero_extend_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.zero_extend i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.zero_extend i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases zero_extend_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem sign_extend_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.sign_extend i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.sign_extend i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases sign_extend_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem rotate_left_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_left i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.rotate_left i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases rotate_left_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem rotate_right_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.rotate_right i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.rotate_right i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases rotate_right_args_of_non_none hTerm with
    ⟨_i, w, _hI, hA, _hi⟩
  exact ⟨SmtType.BitVec w, hA, by simp, by simp⟩

private theorem int_to_bv_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (SmtTerm.int_to_bv i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.int_to_bv i a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases int_to_bv_args_of_non_none hTerm with
    ⟨_i, _hI, hA, _hi⟩
  exact ⟨SmtType.Int, hA, by simp, by simp⟩

private theorem is_arg_non_reg_of_non_none
    (idx : Term) (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx)) a) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTester :
      (∃ s d i,
          __eo_to_smt_tester (__eo_to_smt idx) =
            SmtTerm.DtTester s d i) ∨
        __eo_to_smt_tester (__eo_to_smt idx) = SmtTerm.None := by
    cases __eo_to_smt idx <;> simp [__eo_to_smt_tester]
  rcases hTester with ⟨s, d, i, hTester⟩ | hTester
  · have hTerm :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) a) := by
      unfold term_has_non_none_type
      simpa [hTester] using hNN
    exact ⟨SmtType.Datatype s d,
      dt_tester_arg_datatype_of_non_none hTerm, by simp, by simp⟩
  · exfalso
    apply hNN
    simp [hTester, __smtx_typeof, __smtx_typeof_apply]

private theorem dt_sel_arg_non_reg_of_non_none
    (s : native_String) (d : Datatype) (i j : native_Nat) (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) a) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hSel :
      (∃ (ss : native_String) (dd : SmtDatatype) (ii jj : native_Nat),
          __eo_to_smt (Term.DtSel s d i j) =
            SmtTerm.DtSel ss dd ii jj) ∨
        __eo_to_smt (Term.DtSel s d i j) = SmtTerm.None := by
    rw [TranslationProofs.eo_to_smt_term_dt_sel]
    cases TranslationProofs.__eo_reserved_datatype_name s <;>
      simp [native_ite]
  rcases hSel with ⟨ss, dd, ii, jj, hSel⟩ | hSel
  · have hTerm :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel ss dd ii jj) a) := by
      unfold term_has_non_none_type
      simpa [hSel] using hNN
    exact ⟨SmtType.Datatype ss dd,
      dt_sel_arg_datatype_of_non_none hTerm, by simp, by simp⟩
  · exfalso
    apply hNN
    simp [hSel, __smtx_typeof, __smtx_typeof_apply]

private theorem bv_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
  rcases bv_binop_args_of_non_none (op := op) (hTy a b) hTerm with
    ⟨w, hA, hB⟩
  exact ⟨SmtType.BitVec w, SmtType.BitVec w, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem bv_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
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
  rcases bv_binop_ret_args_of_non_none (op := op) (ret := R)
      (hTy a b) hTerm with
    ⟨w, hA, hB⟩
  exact ⟨SmtType.BitVec w, SmtType.BitVec w, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem bv_concat_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.concat a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.concat a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases bv_concat_args_of_non_none hTerm with
    ⟨wA, wB, hA, hB⟩
  exact ⟨SmtType.BitVec wA, SmtType.BitVec wB, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_arg_of_non_none (op := op) (hTy a) hTerm with
    ⟨T, hA⟩
  exact ⟨SmtType.Seq T, hA, by simp, by simp⟩

private theorem seq_unop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_arg_of_non_none_ret (op := op) (R := R) (hTy a)
      hTerm with
    ⟨T, hA⟩
  exact ⟨SmtType.Seq T, hA, by simp, by simp⟩

private theorem seq_char_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a)
            (SmtType.Seq SmtType.Char)) R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hA :
      __smtx_typeof a = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) (ret := R) (hTy a) hTerm
  exact ⟨SmtType.Seq SmtType.Char, hA, by simp, by simp⟩

private theorem seq_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
  rcases seq_binop_args_of_non_none (op := op) (hTy a b)
      hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
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
  rcases seq_binop_args_of_non_none_ret (op := op) (R := R)
      (hTy a b) hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_char_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
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
  rcases seq_char_binop_args_of_non_none (op := op) (ret := R)
      (hTy a b) hTerm with
    ⟨hA, hB⟩
  exact ⟨SmtType.Seq SmtType.Char, SmtType.Seq SmtType.Char, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_triop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          __smtx_typeof_seq_op_3
            (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c))
    (a b c : SmtTerm) :
    __smtx_typeof (op a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_triop_args_of_non_none (op := op) (hTy a b c)
      hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, SmtType.Seq T,
    hA, hB, hC, by simp, by simp, by simp, by simp, by simp, by simp⟩

private theorem seq_nth_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_nth a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.seq_nth a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases seq_nth_args_of_non_none hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Int, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem seq_unit_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Seq (__smtx_typeof a))
          (SmtType.Seq (__smtx_typeof a)) ≠ SmtType.None := by
    simpa [__smtx_typeof.eq_119] using hNN
  have hSeqWf :
      __smtx_type_wf (SmtType.Seq (__smtx_typeof a)) = true :=
    smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Seq (__smtx_typeof a))
      (SmtType.Seq (__smtx_typeof a)) hGuardNN
  have hSeqWfRec :
      __smtx_type_wf_rec (SmtType.Seq (__smtx_typeof a))
        native_reflist_nil = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using hSeqWf
  have hArgWfRec :
      __smtx_type_wf_rec (__smtx_typeof a) native_reflist_nil = true :=
    TranslationProofs.seq_type_wf_rec_component_of_wf hSeqWfRec
  exact ⟨__smtx_typeof a, rfl,
    by
      intro hNone
      rw [hNone] at hArgWfRec
      simp [__smtx_type_wf_rec] at hArgWfRec,
    type_wf_rec_ne_reglan hArgWfRec⟩

private theorem set_singleton_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Set (__smtx_typeof a))
          (SmtType.Set (__smtx_typeof a)) ≠ SmtType.None := by
    simpa [__smtx_typeof.eq_122] using hNN
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof a)) = true :=
    smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Set (__smtx_typeof a))
      (SmtType.Set (__smtx_typeof a)) hGuardNN
  have hSetWfRec :
      __smtx_type_wf_rec (SmtType.Set (__smtx_typeof a))
        native_reflist_nil = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using hSetWf
  have hArgWfRec :
      __smtx_type_wf_rec (__smtx_typeof a) native_reflist_nil = true :=
    TranslationProofs.set_type_wf_rec_component_of_wf hSetWfRec
  exact ⟨__smtx_typeof a, rfl,
    by
      intro hNone
      rw [hNone] at hArgWfRec
      simp [__smtx_type_wf_rec] at hArgWfRec,
    type_wf_rec_ne_reglan hArgWfRec⟩

private theorem str_substr_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_substr a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_substr a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_substr_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Int, SmtType.Int, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

private theorem str_indexof_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_indexof a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_indexof a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_indexof_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Seq T, SmtType.Int, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

private theorem str_at_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.str_at a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_at a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_at_args_of_non_none hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Seq T, SmtType.Int, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem str_update_args_non_reg_of_non_none
    (a b c : SmtTerm) :
    __smtx_typeof (SmtTerm.str_update a b c) ≠ SmtType.None ->
      ∃ A B C,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          __smtx_typeof c = C ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
          C ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.str_update a b c) := by
    unfold term_has_non_none_type
    exact hNN
  rcases str_update_args_of_non_none hTerm with
    ⟨T, hA, hB, hC⟩
  exact ⟨SmtType.Seq T, SmtType.Int, SmtType.Seq T, hA, hB, hC,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

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
    (by intro a b; rw [__smtx_model_eval.eq_12])
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
    (by intro a b; rw [__smtx_model_eval.eq_13])
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
    (by intro a b; rw [__smtx_model_eval.eq_14])
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
    (by intro a b; rw [__smtx_model_eval.eq_15])
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
    (by intro a b; rw [__smtx_model_eval.eq_16])
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
    (by intro a b; rw [__smtx_model_eval.eq_17])
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
    (by intro a b; rw [__smtx_model_eval.eq_18])
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
    (by intro a; rw [__smtx_model_eval.eq_19])
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
    (by intro a; rw [__smtx_model_eval.eq_20])
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
    (by intro a; rw [__smtx_model_eval.eq_21])
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
    (by intro a; rw [__smtx_model_eval.eq_22])
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
    (by intro a; rw [__smtx_model_eval.eq_23])
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
    (by intro a b; rw [__smtx_model_eval.eq_24])
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
    (by intro a b; rw [__smtx_model_eval.eq_25])
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
    (by intro a b; rw [__smtx_model_eval.eq_26])
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
    (by intro a b; rw [__smtx_model_eval.eq_30])
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
    (by intro a b; rw [__smtx_model_eval.eq_31])
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
    (by intro a b; rw [__smtx_model_eval.eq_32])
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
    (by intro a b; rw [__smtx_model_eval.eq_27])
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
    (by intro a; rw [__smtx_model_eval.eq_28])
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
    (by intro a; rw [__smtx_model_eval.eq_29])
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

private def intIspow2Term (a : SmtTerm) : SmtTerm :=
  SmtTerm.and (SmtTerm.geq a (SmtTerm.Numeral 0))
    (SmtTerm.eq a (SmtTerm.int_pow2 (SmtTerm.int_log2 a)))

private noncomputable def intIspow2Eval (a : SmtValue) : SmtValue :=
  __smtx_model_eval_and
    (__smtx_model_eval_geq a (SmtValue.Numeral 0))
    (__smtx_model_eval_eq a
      (__smtx_model_eval_int_pow2 (__smtx_model_eval_int_log2 a)))

private theorem int_ispow2_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (intIspow2Term a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hAnd := smt_typeof_and_args_bool_of_non_none
    (SmtTerm.geq a (SmtTerm.Numeral 0))
    (SmtTerm.eq a (SmtTerm.int_pow2 (SmtTerm.int_log2 a)))
    (by simpa [intIspow2Term] using hNN)
  have hGeqNN : __smtx_typeof (SmtTerm.geq a (SmtTerm.Numeral 0)) ≠
      SmtType.None := by
    rw [hAnd.1]
    simp
  rcases arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.geq
      SmtType.Bool (by intro x y; exact typeof_geq_eq x y)
      a (SmtTerm.Numeral 0) hGeqNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem congTrueSpine_int_ispow2_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_ispow2 intIspow2Term
    intIspow2Eval
    (by intro a; rfl)
    int_ispow2_arg_non_reg_of_non_none
    (by
      intro a
      rw [intIspow2Term, intIspow2Eval, __smtx_model_eval.eq_8,
        __smtx_model_eval.eq_18, __smtx_model_eval.eq_134,
        __smtx_model_eval.eq_28, __smtx_model_eval.eq_29,
        __smtx_model_eval.eq_2])
    x rhs

private theorem congTypeSpine_int_ispow2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_ispow2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_ispow2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_ispow2
    intIspow2Term
    (by intro a; rfl)
    (by
      intro a b h
      rw [intIspow2Term, intIspow2Term, typeof_and_eq, typeof_and_eq,
        typeof_geq_eq, typeof_geq_eq, typeof_eq_eq, typeof_eq_eq,
        typeof_int_pow2_eq, typeof_int_pow2_eq, typeof_int_log2_eq,
        typeof_int_log2_eq, h])
    x rhs

private theorem congTrueSpine_int_div_by_zero_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_int_div_by_zero
    (fun a => SmtTerm.div a (SmtTerm.Numeral 0))
    (fun v => smtEvalDiv M v (SmtValue.Numeral 0))
    (by intro a; rfl)
    div_by_zero_arg_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_24, __smtx_model_eval.eq_2])
    x rhs

private theorem congTypeSpine_int_div_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_int_div_by_zero
    (fun a => SmtTerm.div a (SmtTerm.Numeral 0))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_div_eq, typeof_div_eq, h])
    x rhs

private theorem congTrueSpine_mod_by_zero_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_mod_by_zero
    (fun a => SmtTerm.mod a (SmtTerm.Numeral 0))
    (fun v => smtEvalMod M v (SmtValue.Numeral 0))
    (by intro a; rfl)
    mod_by_zero_arg_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_25, __smtx_model_eval.eq_2])
    x rhs

private theorem congTypeSpine_mod_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_mod_by_zero
    (fun a => SmtTerm.mod a (SmtTerm.Numeral 0))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_mod_eq, typeof_mod_eq, h])
    x rhs

private theorem congTrueSpine_qdiv_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.qdiv SmtTerm.qdiv
    (smtEvalQdiv M)
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv
      SmtType.Real (by intro a b; exact typeof_qdiv_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_128])
    x₁ x₂ rhs

private theorem congTypeSpine_qdiv_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.qdiv SmtTerm.qdiv
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_qdiv_eq, typeof_qdiv_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_qdiv_total_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.qdiv_total
    SmtTerm.qdiv_total
    __smtx_model_eval_qdiv_total
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.qdiv_total
      SmtType.Real (by intro a b; exact typeof_qdiv_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_129])
    x₁ x₂ rhs

private theorem congTypeSpine_qdiv_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.qdiv_total
    SmtTerm.qdiv_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_qdiv_total_eq, typeof_qdiv_total_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_qdiv_by_zero_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp._at_div_by_zero
    (fun a => SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1)))
    (fun v => smtEvalQdiv M v
      (SmtValue.Rational (native_mk_rational 0 1)))
    (by intro a; rfl)
    qdiv_by_zero_arg_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_128, __smtx_model_eval.eq_3])
    x rhs

private theorem congTypeSpine_qdiv_by_zero_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp._at_div_by_zero
    (fun a => SmtTerm.qdiv a (SmtTerm.Rational (native_mk_rational 0 1)))
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_qdiv_eq, typeof_qdiv_eq, h])
    x rhs

private theorem congTrueSpine_bv_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_unop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x rhs

private theorem congTypeSpine_bv_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

private theorem congTrueSpine_bv_unop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_unop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

private theorem congTypeSpine_bv_unop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_bv_op_1_ret (__smtx_typeof a) R)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

private theorem congTrueSpine_bv_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_bv_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_bv_binop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (bv_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_bv_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private def bvPredToBv (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (a b : SmtTerm) : SmtTerm :=
  SmtTerm.ite (pred a b) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)

private def bvPredToBvEval (predEval : SmtValue -> SmtValue -> SmtValue)
    (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_ite (predEval a b)
    (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)

private def bvBitTerm (i a : SmtTerm) : SmtTerm :=
  SmtTerm.eq (SmtTerm.extract i i a) (SmtTerm.Binary 1 1)

private theorem bv_pred_to_bv_args_non_reg_of_non_none
    (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (a b : SmtTerm) :
    __smtx_typeof (bvPredToBv pred a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (bvPredToBv pred a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases ite_args_of_non_none hTerm with ⟨_T, hCond, _hThen, _hElse, _hT⟩
  have hPredNN : __smtx_typeof (pred a b) ≠ SmtType.None := by
    rw [hCond]
    simp
  exact bv_binop_ret_args_non_reg_of_non_none pred SmtType.Bool hTy
    a b hPredNN

private theorem bv_bit_arg_non_reg_of_non_none
    (i a : SmtTerm) :
    __smtx_typeof (bvBitTerm i a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (SmtTerm.extract i i a))
          (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    simpa [bvBitTerm, typeof_eq_eq] using hNN
  have hExtractNN : __smtx_typeof (SmtTerm.extract i i a) ≠ SmtType.None :=
    (cong_smtx_typeof_eq_non_none hEqNN).2
  exact extract_arg_non_reg_of_non_none i i a hExtractNN

private theorem congTrueSpine_bv_pred_to_bv_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (predEval : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          bvPredToBv pred (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (bvPredToBv pred a b) =
          bvPredToBvEval predEval
            (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp (bvPredToBv pred)
    (bvPredToBvEval predEval) hToSmt
    (bv_pred_to_bv_args_non_reg_of_non_none pred hTy) hEval
    x₁ x₂ rhs

private theorem congTypeSpine_bv_pred_to_bv_eq_has_bool_type
    (eoOp : UserOp) (pred : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          bvPredToBv pred (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (pred a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) SmtType.Bool)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp (bvPredToBv pred)
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [bvPredToBv, bvPredToBv, typeof_ite_eq, typeof_ite_eq,
        hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private noncomputable def bvZeroTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof a)) 0

private noncomputable def bvAllOnesTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvnot (bvZeroTerm a)

private noncomputable def bvRedandTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvcomp a (bvAllOnesTerm a)

private noncomputable def bvRedorTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.bvnot (SmtTerm.bvcomp a (bvZeroTerm a))

private theorem bvredand_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (bvRedandTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  rcases bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvcomp
      (SmtType.BitVec 1)
      (by intro x y; rw [__smtx_typeof.eq_45])
      a (bvAllOnesTerm a) (by simpa [bvRedandTerm] using hNN) with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem bvredor_arg_non_reg_of_non_none (a : SmtTerm) :
    __smtx_typeof (bvRedorTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hInnerNN :
      __smtx_typeof (SmtTerm.bvcomp a (bvZeroTerm a)) ≠ SmtType.None := by
    rcases bv_unop_args_non_reg_of_non_none SmtTerm.bvnot
        (by intro x; rw [__smtx_typeof.eq_38])
        (SmtTerm.bvcomp a (bvZeroTerm a))
        (by simpa [bvRedorTerm] using hNN) with
      ⟨A, hA, hANN, _hAReg⟩
    rw [hA]
    exact hANN
  rcases bv_binop_ret_args_non_reg_of_non_none SmtTerm.bvcomp
      (SmtType.BitVec 1)
      (by intro x y; rw [__smtx_typeof.eq_45])
      a (bvZeroTerm a) hInnerNN with
    ⟨A, _B, hA, _hB, hANN, _hBNN, hAReg, _hBReg⟩
  exact ⟨A, hA, hANN, hAReg⟩

private theorem congTrueSpine_bvredand_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.bvredand) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true_of_eval_congr M hM UserOp.bvredand
    bvRedandTerm
    (by intro a; rfl)
    bvredand_arg_non_reg_of_non_none
    (by
      intro a b hTy hEval
      rw [bvRedandTerm, bvAllOnesTerm, bvZeroTerm, bvRedandTerm,
        bvAllOnesTerm, bvZeroTerm, __smtx_model_eval.eq_45,
        __smtx_model_eval.eq_45, __smtx_model_eval.eq_38,
        __smtx_model_eval.eq_38, __smtx_model_eval.eq_5,
        __smtx_model_eval.eq_5, hTy, hEval])
    x rhs

private theorem congTypeSpine_bvredand_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.bvredand) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.bvredand) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredand) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.bvredand
    bvRedandTerm
    (by intro a; rfl)
    (by
      intro a b h
      rw [bvRedandTerm, bvAllOnesTerm, bvZeroTerm, bvRedandTerm,
        bvAllOnesTerm, bvZeroTerm, __smtx_typeof.eq_45,
        __smtx_typeof.eq_45, __smtx_typeof.eq_38, __smtx_typeof.eq_38,
        __smtx_typeof.eq_5, __smtx_typeof.eq_5, h])
    x rhs

private theorem congTrueSpine_bvredor_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.bvredor) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true_of_eval_congr M hM UserOp.bvredor
    bvRedorTerm
    (by intro a; rfl)
    bvredor_arg_non_reg_of_non_none
    (by
      intro a b hTy hEval
      rw [bvRedorTerm, bvZeroTerm, bvRedorTerm, bvZeroTerm,
        __smtx_model_eval.eq_38, __smtx_model_eval.eq_38,
        __smtx_model_eval.eq_45, __smtx_model_eval.eq_45,
        __smtx_model_eval.eq_5, __smtx_model_eval.eq_5, hTy, hEval])
    x rhs

private theorem congTypeSpine_bvredor_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.bvredor) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.bvredor) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.bvredor) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.bvredor
    bvRedorTerm
    (by intro a; rfl)
    (by
      intro a b h
      rw [bvRedorTerm, bvZeroTerm, bvRedorTerm, bvZeroTerm,
        __smtx_typeof.eq_38, __smtx_typeof.eq_38, __smtx_typeof.eq_45,
        __smtx_typeof.eq_45, __smtx_typeof.eq_5, __smtx_typeof.eq_5, h])
    x rhs

private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hWidth : native_zleq 0 1 = true := by native_decide
  have hMod : native_zeq 1 (native_mod_total 1 (native_int_pow2 1)) = true := by
    native_decide
  have hNat : native_int_to_nat 1 = 1 := by native_decide
  unfold __smtx_typeof
  simp [native_ite, SmtEval.native_and, hWidth, hMod, hNat]

private def bvIteTerm (c t e : SmtTerm) : SmtTerm :=
  SmtTerm.ite (SmtTerm.eq c (SmtTerm.Binary 1 1)) t e

private theorem congTrueSpine_bvite_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (c t e rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.bvite c t e rhs hSpine with
    ⟨c', t', e', hRhs, hCond, hThen, hElse⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let C : SmtTerm := __eo_to_smt c
    let T : SmtTerm := __eo_to_smt t
    let E : SmtTerm := __eo_to_smt e
    let C' : SmtTerm := __eo_to_smt c'
    let T' : SmtTerm := __eo_to_smt t'
    let E' : SmtTerm := __eo_to_smt e'
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c') t') e')
        hEqBool
    have hLeftNN :
        __smtx_typeof (bvIteTerm C T E) ≠ SmtType.None := by
      simpa [C, T, E, bvIteTerm] using hTypes.2
    have hIteNN : term_has_non_none_type (bvIteTerm C T E) := by
      unfold term_has_non_none_type
      exact hLeftNN
    rcases ite_args_of_non_none hIteNN with
      ⟨_R, hCondTy, _hThenTy, _hElseTy, _hRNN⟩
    have hCondNN :
        __smtx_typeof (SmtTerm.eq C (SmtTerm.Binary 1 1)) ≠
          SmtType.None := by
      rw [hCondTy]
      simp
    have hCondEqNN :
        __smtx_typeof_eq
            (__smtx_typeof C) (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
          SmtType.None := by
      simpa [typeof_eq_eq] using hCondNN
    have hEqArgs := cong_smtx_typeof_eq_non_none hCondEqNN
    have hCReg : __smtx_typeof C ≠ SmtType.RegLan := by
      rw [hEqArgs.1, typeof_binary_one_eq]
      simp
    have hCondTyEq : __smtx_typeof C = __smtx_typeof C' :=
      smt_type_eq_of_eq_true_or_same M c c' hCond
    have hCondEval :
        __smtx_model_eval M C = __smtx_model_eval M C' :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM c c'
        (__smtx_typeof C) rfl (by rw [← hCondTyEq])
        hEqArgs.2 hCReg hCond
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (bvIteTerm C T E))
        (__smtx_model_eval M (bvIteTerm C' T' E'))
    rw [bvIteTerm, bvIteTerm, __smtx_model_eval.eq_133,
      __smtx_model_eval.eq_133, __smtx_model_eval.eq_134,
      __smtx_model_eval.eq_134, hCondEval]
    rcases smtx_model_eval_eq_boolean
        (__smtx_model_eval M C')
        (__smtx_model_eval M (SmtTerm.Binary 1 1)) with ⟨b, hb⟩
    rw [hb]
    cases b with
    | false =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M e e' hElse
    | true =>
        simpa [__smtx_model_eval_ite] using
          smt_value_rel_of_eq_true_or_same M t t' hThen

private theorem congTypeSpine_bvite_eq_has_bool_type
    (c t e rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e)
        rhs) :=
  congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.bvite bvIteTerm
    (by intro a b c; rfl)
    (by
      intro a b c a' b' c' ha hb hc
      rw [bvIteTerm, bvIteTerm, typeof_ite_eq, typeof_ite_eq,
        typeof_eq_eq, typeof_eq_eq, ha, hb, hc])
    c t e rhs

private def bvFromBoolsTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.concat
    (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) b

private def bvFromBoolsEval (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_concat
    (__smtx_model_eval_ite a (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)) b

private theorem bv_from_bools_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (bvFromBoolsTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases bv_concat_args_non_reg_of_non_none
      (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) b
      (by simpa [bvFromBoolsTerm] using hNN) with
    ⟨I, B, hI, hB, hINN, hBNN, _hIReg, hBReg⟩
  have hIteNN :
      __smtx_typeof
          (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
        SmtType.None := by
    rw [hI]
    exact hINN
  have hIteTerm :
      term_has_non_none_type
        (SmtTerm.ite a (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    exact hIteNN
  rcases ite_args_of_non_none hIteTerm with
    ⟨_T, hA, _hThen, _hElse, _hTNN⟩
  exact ⟨SmtType.Bool, B, hA, hB, by simp, hBNN, by simp, hBReg⟩

private theorem congTrueSpine_bv_from_bools_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp._at_from_bools
    bvFromBoolsTerm bvFromBoolsEval
    (by intro a b; rfl)
    bv_from_bools_args_non_reg_of_non_none
    (by
      intro a b
      rw [bvFromBoolsTerm, bvFromBoolsEval, __smtx_model_eval.eq_35,
        __smtx_model_eval.eq_133, __smtx_model_eval.eq_5,
        __smtx_model_eval.eq_5])
    x₁ x₂ rhs

private theorem congTypeSpine_bv_from_bools_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp._at_from_bools
    bvFromBoolsTerm
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [bvFromBoolsTerm, bvFromBoolsTerm, typeof_concat_eq,
        typeof_concat_eq, typeof_ite_eq, typeof_ite_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_bv_concat_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.concat SmtTerm.concat
    __smtx_model_eval_concat
    (by intro a b; rfl)
    bv_concat_args_non_reg_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_35])
    x₁ x₂ rhs

private theorem congTypeSpine_bv_concat_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.concat SmtTerm.concat
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_concat_eq, typeof_concat_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_seq_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_unop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x rhs

private theorem congTypeSpine_seq_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1 (__smtx_typeof a))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

private theorem congTrueSpine_seq_unop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_unop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

private theorem congTypeSpine_seq_unop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          __smtx_typeof_seq_op_1_ret (__smtx_typeof a) R)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

private theorem congTrueSpine_seq_char_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            R SmtType.None)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_char_unop_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x rhs

private theorem congTypeSpine_seq_char_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTy :
      ∀ a,
        __smtx_typeof (smtOp a) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            R SmtType.None)
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b h
      rw [hTy a, hTy b, h])
    x rhs

private theorem congTrueSpine_seq_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_seq_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_seq_binop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_seq_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_seq_char_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None)
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (seq_char_binop_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_seq_char_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_str_in_re_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.str_in_re x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y₁) y₂)
        hEqBool
    have hLeftNN :
        __smtx_typeof (SmtTerm.str_in_re X₁ X₂) ≠ SmtType.None := by
      simpa [X₁, X₂] using hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.str_in_re X₁ X₂) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      seq_char_reglan_args_of_non_none
        (op := SmtTerm.str_in_re) (typeof_str_in_re_eq X₁ X₂) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_in_re X₁ X₂))
        (__smtx_model_eval M (SmtTerm.str_in_re Y₁ Y₂)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_118, __smtx_model_eval.eq_118,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval]
    simp [__smtx_model_eval_str_in_re, __smtx_model_eval_eq,
      native_veq, hExt (native_unpack_string sx)]

private theorem congTypeSpine_str_in_re_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.str_in_re
    SmtTerm.str_in_re
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_str_in_re_eq, typeof_str_in_re_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_re_comp_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_comp) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_comp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_comp) x)
        (Term.Apply (Term.UOp UserOp.re_comp) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_comp X) ≠ SmtType.None := by
      simpa [X] using hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_comp X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_comp)
        (typeof_re_comp_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExtComp : ∀ str,
        native_str_in_re str (native_re_comp rx) =
          native_str_in_re str (native_re_comp ry) := by
      intro str
      rw [native_str_in_re_re_comp, native_str_in_re_re_comp, hExt str]
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_comp X))
        (__smtx_model_eval M (SmtTerm.re_comp Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_111, __smtx_model_eval.eq_111, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_comp, __smtx_model_eval_eq, hExtComp]

private theorem congTypeSpine_re_comp_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.re_comp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.re_comp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_comp) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_comp
    SmtTerm.re_comp
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_re_comp_eq, typeof_re_comp_eq, h])
    x rhs

private theorem congTrueSpine_re_opt_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.re_opt) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.re_opt x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    let eps : native_RegLan :=
      native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.re_opt) x)
        (Term.Apply (Term.UOp UserOp.re_opt) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_opt X) ≠ SmtType.None := by
      simpa [X] using hTypes.2
    have hTerm : term_has_non_none_type (SmtTerm.re_opt X) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hXTy : __smtx_typeof X = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_opt)
        (typeof_re_opt_eq X) hTerm
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    have hExtOpt : ∀ str,
        native_str_in_re str (native_re_union rx eps) =
          native_str_in_re str (native_re_union ry eps) := by
      intro str
      rw [native_str_in_re_re_union, native_str_in_re_re_union, hExt str]
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.re_opt X))
        (__smtx_model_eval M (SmtTerm.re_opt Y)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_110, __smtx_model_eval.eq_110, hXEval,
      hYEval]
    simp [__smtx_model_eval_re_opt, __smtx_model_eval_re_union,
      __smtx_model_eval_eq, eps, hExtOpt]

private theorem congTypeSpine_re_opt_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.re_opt) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.re_opt) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.re_opt) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_opt
    SmtTerm.re_opt
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_re_opt_eq, typeof_re_opt_eq, h])
    x rhs

private def nativeReEpsilon : native_RegLan :=
  native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))

private def nativeReExpRec : native_Nat -> native_RegLan -> native_RegLan
  | native_nat_zero, _ => nativeReEpsilon
  | native_nat_succ n, r => native_re_concat (nativeReExpRec n r) r

private theorem model_eval_re_exp_rec_reglan_eq :
    ∀ n r,
      __smtx_model_eval_re_exp_rec n (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReExpRec n r) := by
  intro n
  induction n with
  | zero =>
      intro r
      rfl
  | succ n ih =>
      intro r
      simp [__smtx_model_eval_re_exp_rec, nativeReExpRec, ih,
        __smtx_model_eval_re_concat]

private theorem native_str_in_re_re_exp_rec_congr :
    ∀ n r r',
      (∀ str, native_str_in_re str r = native_str_in_re str r') ->
      ∀ str,
        native_str_in_re str (nativeReExpRec n r) =
          native_str_in_re str (nativeReExpRec n r') := by
  intro n
  induction n with
  | zero =>
      intro r r' h str
      rfl
  | succ n ih =>
      intro r r' h str
      simpa [nativeReExpRec] using
        native_str_in_re_re_concat_congr str
          (nativeReExpRec n r) (nativeReExpRec n r') r r'
          (fun s => ih r r' h s) h

private theorem smt_value_rel_re_exp_reglan_congr
    (n : native_Int) {r r' : native_RegLan}
    (hExt : ∀ str, native_str_in_re str r = native_str_in_re str r') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_exp (SmtValue.Numeral n) (SmtValue.RegLan r))
      (__smtx_model_eval_re_exp (SmtValue.Numeral n) (SmtValue.RegLan r')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  have hExtExp :
      ∀ str,
        native_str_in_re str (nativeReExpRec (native_int_to_nat n) r) =
          native_str_in_re str (nativeReExpRec (native_int_to_nat n) r') :=
    native_str_in_re_re_exp_rec_congr (native_int_to_nat n) r r' hExt
  simp [__smtx_model_eval_re_exp, model_eval_re_exp_rec_reglan_eq,
    __smtx_model_eval_eq, hExtExp]

private theorem re_exp_index_arg_of_non_none (idx t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_exp idx t) ≠ SmtType.None ->
      ∃ k,
        idx = SmtTerm.Numeral k ∧ __smtx_typeof t = SmtType.RegLan := by
  intro hNN
  cases idx <;> simp [typeof_re_exp_eq, __smtx_typeof_re_exp] at hNN
  case Numeral k =>
    have hTerm : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral k) t) := by
      unfold term_has_non_none_type
      rw [typeof_re_exp_eq]
      exact hNN
    exact ⟨k, rfl, (re_exp_arg_of_non_none hTerm).2⟩

private def nativeReLoopRec :
    native_Nat -> native_Int -> native_Int -> native_RegLan -> native_RegLan
  | native_nat_zero, lo, _hi, r => nativeReExpRec (native_int_to_nat lo) r
  | native_nat_succ n, lo, hi, r =>
      native_re_union
        (nativeReLoopRec n lo (native_zplus hi (native_zneg 1)) r)
        (nativeReExpRec (native_int_to_nat hi) r)

private theorem model_eval_re_loop_rec_reglan_eq :
    ∀ n lo hi r,
      __smtx_model_eval_re_loop_rec n (SmtValue.Numeral lo)
          (SmtValue.Numeral hi) (SmtValue.RegLan r) =
        SmtValue.RegLan (nativeReLoopRec n lo hi r) := by
  intro n
  induction n with
  | zero =>
      intro lo hi r
      simp [__smtx_model_eval_re_loop_rec, nativeReLoopRec,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp]
  | succ n ih =>
      intro lo hi r
      simp [__smtx_model_eval_re_loop_rec, nativeReLoopRec, ih,
        model_eval_re_exp_rec_reglan_eq, __smtx_model_eval_re_exp,
        __smtx_model_eval_re_union]

private theorem native_str_in_re_re_loop_rec_congr :
    ∀ n lo hi r r',
      (∀ str, native_str_in_re str r = native_str_in_re str r') ->
      ∀ str,
        native_str_in_re str (nativeReLoopRec n lo hi r) =
          native_str_in_re str (nativeReLoopRec n lo hi r') := by
  intro n
  induction n with
  | zero =>
      intro lo hi r r' h str
      simpa [nativeReLoopRec] using
        native_str_in_re_re_exp_rec_congr (native_int_to_nat lo) r r' h str
  | succ n ih =>
      intro lo hi r r' h str
      rw [nativeReLoopRec, nativeReLoopRec, native_str_in_re_re_union,
        native_str_in_re_re_union,
        ih lo (native_zplus hi (native_zneg 1)) r r' h str,
        native_str_in_re_re_exp_rec_congr (native_int_to_nat hi) r r' h str]

private theorem smt_value_rel_re_loop_reglan_congr
    (lo hi : native_Int) {r r' : native_RegLan}
    (hExt : ∀ str, native_str_in_re str r = native_str_in_re str r') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_loop (SmtValue.Numeral lo) (SmtValue.Numeral hi)
        (SmtValue.RegLan r))
      (__smtx_model_eval_re_loop (SmtValue.Numeral lo) (SmtValue.Numeral hi)
        (SmtValue.RegLan r')) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  by_cases hLt : native_zlt hi lo
  · simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite, __smtx_model_eval_eq,
      hLt]
  · have hExtLoop :
        ∀ str,
          native_str_in_re str
              (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
                lo hi r) =
            native_str_in_re str
              (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
                lo hi r') :=
      native_str_in_re_re_loop_rec_congr
        (native_int_to_nat (native_zplus hi (native_zneg lo))) lo hi r r' hExt
    simp [__smtx_model_eval_re_loop, __smtx_model_eval_gt,
      __smtx_model_eval_lt, __smtx_model_eval_ite,
      model_eval_re_loop_rec_reglan_eq, __smtx_model_eval_eq, hLt, hExtLoop]

private theorem re_loop_index_arg_of_non_none (lo hi t : SmtTerm) :
    __smtx_typeof (SmtTerm.re_loop lo hi t) ≠ SmtType.None ->
      ∃ loN hiN,
        lo = SmtTerm.Numeral loN ∧ hi = SmtTerm.Numeral hiN ∧
          __smtx_typeof t = SmtType.RegLan := by
  intro hNN
  cases lo
  case Numeral loN =>
    cases hi
    case Numeral hiN =>
      have hTerm :
          term_has_non_none_type
            (SmtTerm.re_loop (SmtTerm.Numeral loN) (SmtTerm.Numeral hiN) t) := by
        unfold term_has_non_none_type
        exact hNN
      exact ⟨loN, hiN, rfl, rfl, (re_loop_arg_of_non_none hTerm).2.2⟩
    all_goals
      exfalso
      apply hNN
      rw [typeof_re_loop_eq]
      simp [__smtx_typeof_re_loop]
  all_goals
    exfalso
    apply hNN
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop]

private theorem congTrueSpine_re_exp_eq_true
    (M : SmtModel) (hM : model_total_typed M) (n x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_unary_uop_inv M UserOp1.re_exp n x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let I : SmtTerm := __eo_to_smt n
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp1 UserOp1.re_exp n) x)
        (Term.Apply (Term.UOp1 UserOp1.re_exp n) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_exp I X) ≠ SmtType.None := by
      simpa [I, X] using hTypes.2
    rcases re_exp_index_arg_of_non_none I X hLeftNN with
      ⟨k, hI, hXTy⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.re_exp I X))
        (__smtx_model_eval M (SmtTerm.re_exp I Y))
    rw [__smtx_model_eval.eq_109, __smtx_model_eval.eq_109, hI,
      __smtx_model_eval.eq_2, hXEval, hYEval]
    exact smt_value_rel_re_exp_reglan_congr k hExt

private theorem congTrueSpine_re_loop_eq_true
    (M : SmtModel) (hM : model_total_typed M) (lo hi x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed2_unary_uop_inv M UserOp2.re_loop lo hi x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let L : SmtTerm := __eo_to_smt lo
    let H : SmtTerm := __eo_to_smt hi
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)
        (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_loop L H X) ≠ SmtType.None := by
      simpa [L, H, X] using hTypes.2
    rcases re_loop_index_arg_of_non_none L H X hLeftNN with
      ⟨loN, hiN, hL, hH, hXTy⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.re_loop L H X))
        (__smtx_model_eval M (SmtTerm.re_loop L H Y))
    rw [__smtx_model_eval.eq_117, __smtx_model_eval.eq_117, hL, hH,
      __smtx_model_eval.eq_2, __smtx_model_eval.eq_2, hXEval, hYEval]
    exact smt_value_rel_re_loop_reglan_congr loN hiN hExt

private theorem congTrueSpine_reglan_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (nativeOp : native_RegLan -> native_RegLan -> native_RegLan)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          match __smtx_model_eval M a, __smtx_model_eval M b with
          | SmtValue.RegLan r₁, SmtValue.RegLan r₂ =>
              SmtValue.RegLan (nativeOp r₁ r₂)
          | _, _ => SmtValue.NotValue)
    (hExtOp :
      ∀ r₁ r₁' r₂ r₂',
        (∀ str, native_str_in_re str r₁ = native_str_in_re str r₁') ->
        (∀ str, native_str_in_re str r₂ = native_str_in_re str r₂') ->
        ∀ str,
          native_str_in_re str (nativeOp r₁ r₂) =
            native_str_in_re str (nativeOp r₁' r₂'))
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
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
        hEqBool
    have hLeftNN : __smtx_typeof (smtOp X₁ X₂) ≠ SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    have hTerm : term_has_non_none_type (smtOp X₁ X₂) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      reglan_binop_args_of_non_none (op := smtOp) (hTy X₁ X₂) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.RegLan := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₁ hArgs.1 with
      ⟨rx₁, hX₁Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2 with
      ⟨rx₂, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₁ hY₁Ty with
      ⟨ry₁, hY₁Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry₂, hY₂Eval⟩
    have hRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) :=
      smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt₁ : ∀ str,
        native_str_in_re str rx₁ = native_str_in_re str ry₁ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₁
      rw [hX₁Eval, hY₁Eval] at hRel₁
      simpa [__smtx_model_eval_eq] using hRel₁
    have hExt₂ : ∀ str,
        native_str_in_re str rx₂ = native_str_in_re str ry₂ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    have hExt : ∀ str,
        native_str_in_re str (nativeOp rx₁ rx₂) =
          native_str_in_re str (nativeOp ry₁ ry₂) :=
      hExtOp rx₁ ry₁ rx₂ ry₂ hExt₁ hExt₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (smtOp X₁ X₂))
        (__smtx_model_eval M (smtOp Y₁ Y₂)) =
          SmtValue.Boolean true
    rw [hEval, hEval, hX₁Eval, hX₂Eval, hY₁Eval, hY₂Eval]
    simp [__smtx_model_eval_eq, hExt]

private theorem congTrueSpine_re_concat_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_concat
    SmtTerm.re_concat native_re_concat
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_concat_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_113]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str
      exact native_str_in_re_re_concat_congr str r₁ r₁' r₂ r₂' h₁ h₂)
    x₁ x₂ rhs

private theorem congTypeSpine_re_concat_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_concat
    SmtTerm.re_concat
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_concat_eq, typeof_re_concat_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_re_union_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_union
    SmtTerm.re_union native_re_union
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_union_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_115]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str
      rw [native_str_in_re_re_union, native_str_in_re_re_union,
        h₁ str, h₂ str])
    x₁ x₂ rhs

private theorem congTypeSpine_re_union_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_union
    SmtTerm.re_union
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_union_eq, typeof_re_union_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_re_inter_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_inter
    SmtTerm.re_inter native_re_inter
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_inter_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_114]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str
      rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
        h₁ str, h₂ str])
    x₁ x₂ rhs

private theorem congTypeSpine_re_inter_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_inter
    SmtTerm.re_inter
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_inter_eq, typeof_re_inter_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_re_diff_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_diff
    SmtTerm.re_diff native_re_diff
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_diff_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_116]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str
      rw [native_str_in_re_re_diff, native_str_in_re_re_diff,
        h₁ str, h₂ str])
    x₁ x₂ rhs

private theorem congTypeSpine_re_diff_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_diff
    SmtTerm.re_diff
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_diff_eq, typeof_re_diff_eq, ha, hb])
    x₁ x₂ rhs

private theorem set_is_empty_translation_no_type (x : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x)) ≠
      SmtType.None ->
    False := by
  intro hNN
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof_guard_wf
            (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
            (SmtType.Set (__smtx_typeof (__eo_to_smt x)))) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt x)
            (SmtTerm.set_empty (__smtx_typeof (__eo_to_smt x)))) ≠
        SmtType.None at hNN
    rwa [typeof_eq_eq, __smtx_typeof.eq_121] at hNN
  have hEqArgs := cong_smtx_typeof_eq_non_none hEqNN
  exact cong_smt_type_ne_guard_wf_set_full_self hEqArgs.2 hEqArgs.1

private theorem congTrueSpine_set_is_empty_eq_true
    (M : SmtModel) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) true := by
  intro hEqBool _hSpine
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs hEqBool
  exact False.elim (set_is_empty_translation_no_type x hTypes.2)

private theorem congTypeSpine_set_is_empty_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.set_is_empty) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) := by
  intro hTrans _hSpine
  exact False.elim (set_is_empty_translation_no_type x hTrans)

private theorem set_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
  rcases set_binop_args_of_non_none (op := op) (hTy a b)
      hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Set T, SmtType.Set T, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem set_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
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
  rcases set_binop_ret_args_of_non_none (op := op) (T := R)
      (hTy a b) hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Set T, SmtType.Set T, hA, hB,
    by simp, by simp, by simp, by simp⟩

private theorem congTrueSpine_set_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (set_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_set_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_set_binop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
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
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (set_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

private theorem congTypeSpine_set_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private def stringsStoiResultTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.str_to_int (SmtTerm.str_substr a (SmtTerm.Numeral 0) b)

private def stringsStoiResultEval (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_str_to_int
    (__smtx_model_eval_str_substr a (SmtValue.Numeral 0) b)

private theorem strings_stoi_result_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (stringsStoiResultTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases seq_char_unop_args_non_reg_of_non_none SmtTerm.str_to_int
      SmtType.Int (by intro x; exact typeof_str_to_int_eq x)
      (SmtTerm.str_substr a (SmtTerm.Numeral 0) b)
      (by simpa [stringsStoiResultTerm] using hNN) with
    ⟨A, hSubstrA, hANN, _hAReg⟩
  have hSubstrNN :
      __smtx_typeof (SmtTerm.str_substr a (SmtTerm.Numeral 0) b) ≠
        SmtType.None := by
    rw [hSubstrA]
    exact hANN
  rcases str_substr_args_non_reg_of_non_none a (SmtTerm.Numeral 0) b
      hSubstrNN with
    ⟨S, _Z, I, hA, _hZero, hB, hSNN, _hZNN, hINN, hSReg, _hZReg,
      hIReg⟩
  exact ⟨S, I, hA, hB, hSNN, hINN, hSReg, hIReg⟩

private theorem congTrueSpine_strings_stoi_result_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool
        (RuleProofs.smt_value_rel_refl _)
  | app hHead hArg₂ =>
      cases hHead with
      | refl _ =>
          rename_i y₂
          apply RuleProofs.eo_interprets_eq_of_rel M
          · exact hEqBool
          · have hTypes :=
              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (Term.Apply (Term._at_strings_stoi_result x₁) x₂)
                (Term.Apply (Term._at_strings_stoi_result x₁) y₂) hEqBool
            have hxOpNN :
                __smtx_typeof
                    (stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
                  SmtType.None := by
              rw [← show
                __eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) x₂) =
                  stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl]
              exact hTypes.2
            rcases strings_stoi_result_args_non_reg_of_non_none
                (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
              ⟨_A, B, _hx₁A, hx₂B, _hANN, hBNN, _hAReg, hBReg⟩
            have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
              rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ (Or.inr hArg₂)]
              exact hx₂B
            have hEval₂ :
                __smtx_model_eval M (__eo_to_smt x₂) =
                  __smtx_model_eval M (__eo_to_smt y₂) :=
              eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
                B hx₂B hy₂B hBNN hBReg (Or.inr hArg₂)
            have hOpEval :
                __smtx_model_eval M
                    (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) x₂)) =
                  __smtx_model_eval M
                    (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) y₂)) := by
              rw [show
                  __eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) x₂) =
                    stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl,
                show
                  __eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) y₂) =
                    stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt y₂) by rfl]
              rw [stringsStoiResultTerm, stringsStoiResultTerm,
                __smtx_model_eval.eq_95, __smtx_model_eval.eq_95,
                __smtx_model_eval.eq_81, __smtx_model_eval.eq_81,
                __smtx_model_eval.eq_2, hEval₂]
            rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
            rw [hOpEval]
            exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
              (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_strings_stoi_result_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) := by
  intro hTrans hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ rfl hTrans
  | app hHead hArg₂ =>
      cases hHead with
      | refl _ =>
          rename_i y₂
          have hArgTy :
              __smtx_typeof (__eo_to_smt x₂) =
                __smtx_typeof (__eo_to_smt y₂) :=
            smt_type_eq_of_eq_bool_or_same x₂ y₂ (Or.inr hArg₂)
          have hOpTy :
              __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) x₂)) =
                __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) y₂)) := by
            rw [show
                __eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) x₂) =
                  stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl,
              show
                __eo_to_smt (Term.Apply (Term._at_strings_stoi_result x₁) y₂) =
                  stringsStoiResultTerm (__eo_to_smt x₁) (__eo_to_smt y₂) by rfl]
            rw [stringsStoiResultTerm, stringsStoiResultTerm, typeof_str_to_int_eq,
              typeof_str_to_int_eq, typeof_str_substr_eq, typeof_str_substr_eq,
              hArgTy]
          exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
            (Term.Apply (Term._at_strings_stoi_result x₁) x₂)
            (Term.Apply (Term._at_strings_stoi_result x₁) y₂)
            hOpTy hTrans

private def stringsItosResultTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.mod a (SmtTerm.multmult (SmtTerm.Numeral 10) b)

private noncomputable def stringsItosResultEval
    (M : SmtModel) (a b : SmtValue) : SmtValue :=
  smtEvalMod M a (smtEvalMultmult M (SmtValue.Numeral 10) b)

private theorem strings_itos_result_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (stringsItosResultTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
      (by intro x y; exact typeof_mod_eq x y)
      a (SmtTerm.multmult (SmtTerm.Numeral 10) b)
      (by simpa [stringsItosResultTerm] using hNN) with
    ⟨A, C, hA, hMult, hANN, hCNN, hAReg, _hCReg⟩
  have hMultNN :
      __smtx_typeof (SmtTerm.multmult (SmtTerm.Numeral 10) b) ≠
        SmtType.None := by
    rw [hMult]
    exact hCNN
  rcases int_binop_args_non_reg_of_non_none SmtTerm.multmult SmtType.Int
      (by intro x y; exact typeof_multmult_eq x y)
      (SmtTerm.Numeral 10) b hMultNN with
    ⟨_D, B, _hTen, hB, _hDNN, hBNN, _hDReg, hBReg⟩
  exact ⟨A, B, hA, hB, hANN, hBNN, hAReg, hBReg⟩

private theorem congTrueSpine_strings_itos_result_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool
        (RuleProofs.smt_value_rel_refl _)
  | app hHead hArg₂ =>
      cases hHead with
      | refl _ =>
          rename_i y₂
          apply RuleProofs.eo_interprets_eq_of_rel M
          · exact hEqBool
          · have hTypes :=
              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (Term.Apply (Term._at_strings_itos_result x₁) x₂)
                (Term.Apply (Term._at_strings_itos_result x₁) y₂) hEqBool
            have hxOpNN :
                __smtx_typeof
                    (stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
                  SmtType.None := by
              rw [← show
                __eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) x₂) =
                  stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl]
              exact hTypes.2
            rcases strings_itos_result_args_non_reg_of_non_none
                (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
              ⟨_A, B, _hx₁A, hx₂B, _hANN, hBNN, _hAReg, hBReg⟩
            have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
              rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ (Or.inr hArg₂)]
              exact hx₂B
            have hEval₂ :
                __smtx_model_eval M (__eo_to_smt x₂) =
                  __smtx_model_eval M (__eo_to_smt y₂) :=
              eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
                B hx₂B hy₂B hBNN hBReg (Or.inr hArg₂)
            have hOpEval :
                __smtx_model_eval M
                    (__eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) x₂)) =
                  __smtx_model_eval M
                    (__eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) y₂)) := by
              rw [show
                  __eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) x₂) =
                    stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl,
                show
                  __eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) y₂) =
                    stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt y₂) by rfl]
              rw [stringsItosResultTerm, stringsItosResultTerm,
                __smtx_model_eval.eq_25, __smtx_model_eval.eq_25,
                __smtx_model_eval.eq_26, __smtx_model_eval.eq_26,
                __smtx_model_eval.eq_2, hEval₂]
            rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
            rw [hOpEval]
            exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
              (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_strings_itos_result_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) := by
  intro hTrans hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ rfl hTrans
  | app hHead hArg₂ =>
      cases hHead with
      | refl _ =>
          rename_i y₂
          have hArgTy :
              __smtx_typeof (__eo_to_smt x₂) =
                __smtx_typeof (__eo_to_smt y₂) :=
            smt_type_eq_of_eq_bool_or_same x₂ y₂ (Or.inr hArg₂)
          have hOpTy :
              __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) x₂)) =
                __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) y₂)) := by
            rw [show
                __eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) x₂) =
                  stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt x₂) by rfl,
              show
                __eo_to_smt (Term.Apply (Term._at_strings_itos_result x₁) y₂) =
                  stringsItosResultTerm (__eo_to_smt x₁) (__eo_to_smt y₂) by rfl]
            rw [stringsItosResultTerm, stringsItosResultTerm, typeof_mod_eq,
              typeof_mod_eq, typeof_multmult_eq, typeof_multmult_eq, hArgTy]
          exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
            (Term.Apply (Term._at_strings_itos_result x₁) x₂)
            (Term.Apply (Term._at_strings_itos_result x₁) y₂)
            hOpTy hTrans

private def stringsNumOccurTerm (source pattern : SmtTerm) : SmtTerm :=
  SmtTerm.div
    (SmtTerm.neg (SmtTerm.str_len source)
      (SmtTerm.str_len
        (SmtTerm.str_replace_all source pattern
          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
    (SmtTerm.str_len pattern)

private noncomputable def stringsNumOccurEval
    (M : SmtModel) (source pattern : SmtValue) : SmtValue :=
  smtEvalDiv M
    (__smtx_model_eval__
      (__smtx_model_eval_str_len source)
      (__smtx_model_eval_str_len
        (__smtx_model_eval_str_replace_all source pattern
          (SmtValue.Seq (SmtSeq.empty (SmtType.Seq SmtType.Char))))))
    (__smtx_model_eval_str_len pattern)

private theorem strings_num_occur_args_non_reg_of_non_none
    (source pattern : SmtTerm) :
    __smtx_typeof (stringsNumOccurTerm source pattern) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof source = A ∧ __smtx_typeof pattern = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  let replacement :=
    SmtTerm.str_replace_all source pattern
      (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))
  let numerator :=
    SmtTerm.neg (SmtTerm.str_len source) (SmtTerm.str_len replacement)
  rcases int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro x y; exact typeof_div_eq x y)
      numerator (SmtTerm.str_len pattern)
      (by simpa [stringsNumOccurTerm, numerator, replacement] using hNN) with
    ⟨_N, D, hNumerator, hDenominator, hNNumer, hDNN, _hNReg, _hDReg⟩
  have hPatternLenNN :
      __smtx_typeof (SmtTerm.str_len pattern) ≠ SmtType.None := by
    rw [hDenominator]
    exact hDNN
  rcases seq_unop_ret_args_non_reg_of_non_none SmtTerm.str_len SmtType.Int
      (by intro x; exact typeof_str_len_eq x) pattern hPatternLenNN with
    ⟨B, hPattern, hBNN, hBReg⟩
  have hNumeratorNN : __smtx_typeof numerator ≠ SmtType.None := by
    rw [hNumerator]
    exact hNNumer
  rcases arith_overload_binop_args_non_reg_of_non_none SmtTerm.neg
      (by intro x y; exact typeof_neg_eq x y)
      (SmtTerm.str_len source) (SmtTerm.str_len replacement)
      hNumeratorNN with
    ⟨_L, _R, hSourceLen, _hReplacementLen, hLNN, _hRNN, _hLReg, _hRReg⟩
  have hSourceLenNN :
      __smtx_typeof (SmtTerm.str_len source) ≠ SmtType.None := by
    rw [hSourceLen]
    exact hLNN
  rcases seq_unop_ret_args_non_reg_of_non_none SmtTerm.str_len SmtType.Int
      (by intro x; exact typeof_str_len_eq x) source hSourceLenNN with
    ⟨A, hSource, hANN, hAReg⟩
  exact ⟨A, B, hSource, hPattern, hANN, hBNN, hAReg, hBReg⟩

private theorem congTrueSpine_strings_num_occur_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs ->
    eo_interprets M
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp._at_strings_num_occur
    stringsNumOccurTerm (stringsNumOccurEval M)
    (by intro a b; rfl)
    strings_num_occur_args_non_reg_of_non_none
    (by
      intro a b
      rw [stringsNumOccurTerm, stringsNumOccurEval, __smtx_model_eval.eq_24,
        __smtx_model_eval.eq_13, __smtx_model_eval.eq_79,
        __smtx_model_eval.eq_79, __smtx_model_eval.eq_79,
        __smtx_model_eval.eq_99, __smtx_model_eval.eq_78])
    x₁ x₂ rhs

private theorem congTypeSpine_strings_num_occur_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type
    UserOp._at_strings_num_occur stringsNumOccurTerm
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [stringsNumOccurTerm, stringsNumOccurTerm, typeof_div_eq,
        typeof_div_eq, typeof_neg_eq, typeof_neg_eq, typeof_str_len_eq,
        typeof_str_len_eq, typeof_str_len_eq, typeof_str_len_eq,
        typeof_str_len_eq, typeof_str_len_eq, typeof_str_replace_all_eq,
        typeof_str_replace_all_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_str_replace_re_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_replace_re
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.str_replace_re X₁ X₂ X₃) ≠
        SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_replace_re X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      str_replace_re_args_of_non_none
        (op := SmtTerm.str_replace_re)
        (typeof_str_replace_re_eq X₁ X₂ X₃) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        (SmtType.Seq SmtType.Char) hArgs.2.2 hY₃Ty (by simp) (by simp)
        hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_seq_of_smt_type_seq M hM X₃ SmtType.Char hArgs.2.2 with
      ⟨sr, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Seq sr := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_replace_re X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_replace_re Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_100, __smtx_model_eval.eq_100,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_replace_re, __smtx_model_eval_eq,
      native_veq,
      native_str_replace_re_congr (native_unpack_string sx) rx ry
        (native_unpack_string sr) hExt]

private theorem congTrueSpine_str_replace_re_all_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_replace_re_all
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN :
        __smtx_typeof (SmtTerm.str_replace_re_all X₁ X₂ X₃) ≠
          SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_replace_re_all X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      str_replace_re_args_of_non_none
        (op := SmtTerm.str_replace_re_all)
        (typeof_str_replace_re_all_eq X₁ X₂ X₃) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        (SmtType.Seq SmtType.Char) hArgs.2.2 hY₃Ty (by simp) (by simp)
        hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_seq_of_smt_type_seq M hM X₃ SmtType.Char hArgs.2.2 with
      ⟨sr, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Seq sr := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_replace_re_all X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_replace_re_all Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_101, __smtx_model_eval.eq_101,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_replace_re_all, __smtx_model_eval_eq,
      native_veq,
      native_str_replace_re_all_congr (native_unpack_string sx) rx ry
        (native_unpack_string sr) hExt]

private theorem congTrueSpine_str_indexof_re_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_indexof_re
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.str_indexof_re X₁ X₂ X₃) ≠
        SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs := str_indexof_re_args_of_non_none hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Int := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        SmtType.Int hArgs.2.2 hY₃Ty (by simp) (by simp) hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_int_of_smt_type_int M hM X₃ hArgs.2.2 with
      ⟨i, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Numeral i := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_indexof_re X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_indexof_re Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_102, __smtx_model_eval.eq_102,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_indexof_re, __smtx_model_eval_eq,
      native_veq,
      native_str_indexof_re_congr (native_unpack_string sx) rx ry i hExt]

private def stringsStoiNonDigitRegex : SmtTerm :=
  SmtTerm.re_comp (SmtTerm.re_range (SmtTerm.String "0") (SmtTerm.String "9"))

private def stringsStoiNonDigitTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.str_indexof_re a stringsStoiNonDigitRegex (SmtTerm.Numeral 0)

private def stringsStoiNonDigitEval (a : SmtValue) : SmtValue :=
  __smtx_model_eval_str_indexof_re a
    (__smtx_model_eval_re_comp
      (__smtx_model_eval_re_range
        (SmtValue.Seq (native_pack_string "0"))
        (SmtValue.Seq (native_pack_string "9"))))
    (SmtValue.Numeral 0)

private theorem strings_stoi_non_digit_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (stringsStoiNonDigitTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (stringsStoiNonDigitTerm a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArgs := str_indexof_re_args_of_non_none hTerm
  exact ⟨SmtType.Seq SmtType.Char, hArgs.1, by simp, by simp⟩

private theorem congTrueSpine_strings_stoi_non_digit_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) ->
    CongTrueSpine M
      (Term._at_strings_stoi_non_digit x) rhs ->
    eo_interprets M
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) true := by
  intro hEqBool hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool
        (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_strings_stoi_non_digit_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term._at_strings_stoi_non_digit x) ->
    CongTypeSpine
      (Term._at_strings_stoi_non_digit x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) := by
  intro hTrans hSpine
  cases hSpine with
  | refl _ =>
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ rfl hTrans

private theorem congTypeSpine_dt_sel_eq_has_bool_type
    (s : native_String) (d : Datatype) (i j : native_Nat) (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.DtSel s d i j) x) ->
    CongTypeSpine (Term.Apply (Term.DtSel s d i j) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_dt_sel_inv s d i j x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j))
            (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j))
            (__eo_to_smt y))
    cases __eo_to_smt (Term.DtSel s d i j) <;>
      simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.DtSel s d i j) x)
    (Term.Apply (Term.DtSel s d i j) y)
    hOpTy
    hTrans

private theorem congTrueSpine_dt_sel_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i j : native_Nat) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.DtSel s d i j) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_dt_sel_inv M s d i j x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := __eo_to_smt (Term.DtSel s d i j)
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.DtSel s d i j) x)
        (Term.Apply (Term.DtSel s d i j) y)
        hEqBool
    have hxOpNN :
        __smtx_typeof (SmtTerm.Apply F X) ≠ SmtType.None := by
      simpa [F, X] using hTypes.2
    rcases dt_sel_arg_non_reg_of_non_none s d i j X hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof Y = A := by
      rw [← hArgTy]
      exact hxA
    have hEvalArg : __smtx_model_eval M X = __smtx_model_eval M Y :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.Apply F X))
        (__smtx_model_eval M (SmtTerm.Apply F Y)) =
          SmtValue.Boolean true
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) X))
        (__smtx_model_eval M
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) Y)) =
          SmtValue.Boolean true
    rw [TranslationProofs.eo_to_smt_term_dt_sel]
    cases hRes : TranslationProofs.__eo_reserved_datatype_name s
    · simp [hRes, native_ite]
      rw [__smtx_model_eval, __smtx_model_eval, hEvalArg]
      exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
        (RuleProofs.smt_value_rel_refl _)
    · simp [hRes, native_ite, __smtx_model_eval]
      rw [hEvalArg]
      exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
        (RuleProofs.smt_value_rel_refl _)

/--
The remaining typing core for congruence: once the generated program has been
reduced to a spine of congruent applications, the equality between the original
spine and the rewritten spine is Boolean.
-/
private theorem congTypeSpine_refl_eq_has_bool_type (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_bool_type (mkEq t t) := by
  intro hTrans
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t t rfl hTrans

private theorem congTypeSpine_eq_has_bool_type (t rhs : Term) :
    RuleProofs.eo_has_smt_translation t ->
    CongTypeSpine t rhs ->
    __eo_typeof (mkEq t rhs) = Term.Bool ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  intro hTrans hSpine hMkEqType
  match t with
  | Term.Apply (Term.UOp UserOp.not) x =>
      exact congTypeSpine_not_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂ =>
      exact congTypeSpine_eq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e =>
      exact congTypeSpine_ite_eq_has_bool_type c t e rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e =>
      exact congTypeSpine_bvite_eq_has_bool_type c t e rhs hTrans hSpine
  | Term.Apply (Term.Var (Term.String s) T) x =>
      exact congTypeSpine_var_apply_eq_has_bool_type s T x rhs hTrans hSpine
  | Term.Apply (Term.UConst i T) x =>
      exact congTypeSpine_uconst_apply_eq_has_bool_type i T x rhs hTrans hSpine
  | Term.Apply (Term.DtSel s d i j) x =>
      exact congTypeSpine_dt_sel_eq_has_bool_type
        s d i j x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂ =>
      exact congTypeSpine_var_apply_apply_eq_has_bool_type
        s T x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂ =>
      exact congTypeSpine_uconst_apply_apply_eq_has_bool_type
        i T x₁ x₂ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃ =>
      exact congTypeSpine_var_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃ =>
      exact congTypeSpine_uconst_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
      x₄ =>
      exact congTypeSpine_var_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      x₄ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTypeSpine_var_apply_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ x₅ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ x₅ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTypeSpine_var_apply_apply_apply_apply_apply_apply_eq_has_bool_type
        s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hTrans hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_eq_has_bool_type
        i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂ =>
      exact congTypeSpine_and_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂ =>
      exact congTypeSpine_or_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂ =>
      exact congTypeSpine_imp_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂ =>
      exact congTypeSpine_xor_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂ =>
      exact congTypeSpine_plus_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂ =>
      exact congTypeSpine_neg_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂ =>
      exact congTypeSpine_mult_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂ =>
      exact congTypeSpine_lt_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂ =>
      exact congTypeSpine_leq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂ =>
      exact congTypeSpine_gt_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂ =>
      exact congTypeSpine_geq_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.to_real) x =>
      exact congTypeSpine_to_real_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.to_int) x =>
      exact congTypeSpine_to_int_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.is_int) x =>
      exact congTypeSpine_is_int_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.abs) x =>
      exact congTypeSpine_abs_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.__eoo_neg_2) x =>
      exact congTypeSpine_uneg_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂ =>
      exact congTypeSpine_div_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂ =>
      exact congTypeSpine_mod_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂ =>
      exact congTypeSpine_multmult_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂ =>
      exact congTypeSpine_div_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂ =>
      exact congTypeSpine_mod_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂ =>
      exact congTypeSpine_multmult_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂ =>
      exact congTypeSpine_divisible_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_pow2) x =>
      exact congTypeSpine_int_pow2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_log2) x =>
      exact congTypeSpine_int_log2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.int_ispow2) x =>
      exact congTypeSpine_int_ispow2_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x =>
      exact congTypeSpine_int_div_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_mod_by_zero) x =>
      exact congTypeSpine_mod_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.select) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.select
        SmtTerm.select
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_select_eq, typeof_select_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.store
        SmtTerm.store
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_store_eq, typeof_store_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_bvsize) x =>
      exact congTypeSpine_bvsize_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂ =>
      exact congTypeSpine_qdiv_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂ =>
      exact congTypeSpine_qdiv_total_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp._at_div_by_zero) x =>
      exact congTypeSpine_qdiv_by_zero_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_len) x =>
      exact congTypeSpine_seq_unop_ret_eq_has_bool_type UserOp.str_len
        SmtTerm.str_len SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_len_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_rev) x =>
      exact congTypeSpine_seq_unop_eq_has_bool_type UserOp.str_rev
        SmtTerm.str_rev
        (by intro a; rfl)
        (by intro a; exact typeof_str_rev_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_lower) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_lower SmtTerm.str_to_lower (SmtType.Seq SmtType.Char)
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_lower_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_upper) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_upper SmtTerm.str_to_upper (SmtType.Seq SmtType.Char)
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_upper_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_code) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_code_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_from_code) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type
        UserOp.str_from_code SmtTerm.str_from_code
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_str_from_code_eq, typeof_str_from_code_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_is_digit) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_is_digit SmtTerm.str_is_digit SmtType.Bool
        (by intro a; rfl)
        (by intro a; exact typeof_str_is_digit_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_int) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_int_eq a)
        x rhs hTrans hSpine
  | Term._at_strings_stoi_non_digit x =>
      exact congTypeSpine_strings_stoi_non_digit_eq_has_bool_type
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_from_int) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type
        UserOp.str_from_int SmtTerm.str_from_int
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_str_from_int_eq, typeof_str_from_int_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.str_to_re) x =>
      exact congTypeSpine_seq_char_unop_eq_has_bool_type
        UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_re_eq a)
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_mult) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_mult
        SmtTerm.re_mult
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_mult_eq, typeof_re_mult_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_plus) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.re_plus
        SmtTerm.re_plus
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_plus_eq, typeof_re_plus_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.re_exp n) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.re_exp n
        (fun a => SmtTerm.re_exp (__eo_to_smt n) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_exp_eq, typeof_re_exp_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_opt) x =>
      exact congTypeSpine_re_opt_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.re_comp) x =>
      exact congTypeSpine_re_comp_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.re_range SmtTerm.re_range SmtType.RegLan
        (by intro a b; rfl)
        (by intro a b; exact typeof_re_range_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂ =>
      exact congTypeSpine_re_concat_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂ =>
      exact congTypeSpine_re_union_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂ =>
      exact congTypeSpine_re_inter_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂ =>
      exact congTypeSpine_re_diff_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x =>
      exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
        UserOp2.re_loop lo hi
        (fun a => SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_re_loop_eq, typeof_re_loop_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂ =>
      exact congTypeSpine_str_in_re_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x₁) x₂ =>
      exact congTypeSpine_seq_binop_eq_has_bool_type UserOp.str_concat
        SmtTerm.str_concat
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_concat_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x₁) x₂ =>
      exact congTypeSpine_seq_binop_ret_eq_has_bool_type UserOp.str_contains
        SmtTerm.str_contains SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_contains_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.str_at
        SmtTerm.str_at
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_str_at_eq, typeof_str_at_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_prefixof SmtTerm.str_prefixof SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_prefixof_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_suffixof SmtTerm.str_suffixof SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_suffixof_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_lt SmtTerm.str_lt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_lt_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x₁) x₂ =>
      exact congTypeSpine_seq_char_binop_eq_has_bool_type
        UserOp.str_leq SmtTerm.str_leq SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_leq_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.seq_nth
        SmtTerm.seq_nth
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_seq_nth_eq, typeof_seq_nth_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term._at_strings_stoi_result x₁) x₂ =>
      exact congTypeSpine_strings_stoi_result_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term._at_strings_itos_result x₁) x₂ =>
      exact congTypeSpine_strings_itos_result_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂ =>
      exact congTypeSpine_strings_num_occur_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_substr
        SmtTerm.str_substr
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_substr_eq, typeof_str_substr_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_replace
        SmtTerm.str_replace
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_eq, typeof_str_replace_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_indexof
        SmtTerm.str_indexof
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_indexof_eq, typeof_str_indexof_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type UserOp.str_update
        SmtTerm.str_update
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_update_eq, typeof_str_update_eq, ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_all SmtTerm.str_replace_all
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_all_eq, typeof_str_replace_all_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_re SmtTerm.str_replace_re
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_re_eq, typeof_str_replace_re_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_replace_re_all SmtTerm.str_replace_re_all
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_replace_re_all_eq, typeof_str_replace_re_all_eq,
            ha, hb, hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂) x₃ =>
      exact congTypeSpine_typecongr_ternop_eq_has_bool_type
        UserOp.str_indexof_re SmtTerm.str_indexof_re
        (by intro a b c; rfl)
        (by
          intro a b c a' b' c' ha hb hc
          rw [typeof_str_indexof_re_eq, typeof_str_indexof_re_eq, ha, hb,
            hc])
        x₁ x₂ x₃ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.seq_unit) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.seq_unit
        SmtTerm.seq_unit
        (by intro a; rfl)
        (by
          intro a b h
          rw [__smtx_typeof.eq_119, __smtx_typeof.eq_119, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_is_empty) x =>
      exact congTypeSpine_set_is_empty_eq_has_bool_type
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.set_singleton) x =>
      exact congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.set_singleton
        SmtTerm.set_singleton
        (by intro a; rfl)
        (by
          intro a b h
          rw [__smtx_typeof.eq_122, __smtx_typeof.eq_122, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_union
        SmtTerm.set_union
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_union_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_inter
        SmtTerm.set_inter
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_inter_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x₁) x₂ =>
      exact congTypeSpine_set_binop_eq_has_bool_type UserOp.set_minus
        SmtTerm.set_minus
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_minus_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x₁) x₂ =>
      exact congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.set_member
        SmtTerm.set_member
        (by intro a b; rfl)
        (by
          intro a b a' b' ha hb
          rw [typeof_set_member_eq, typeof_set_member_eq, ha, hb])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x₁) x₂ =>
      exact congTypeSpine_set_binop_ret_eq_has_bool_type UserOp.set_subset
        SmtTerm.set_subset SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_subset_eq a b)
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂ =>
      exact congTypeSpine_bv_concat_eq_has_bool_type x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp2 UserOp2.extract i j) x =>
      exact congTypeSpine_typecongr_indexed2_unop_eq_has_bool_type
        UserOp2.extract i j
        (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_extract_eq, typeof_extract_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.repeat i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.repeat i
        (fun a => SmtTerm.repeat (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_repeat_eq, typeof_repeat_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂ =>
      exact congTypeSpine_bv_from_bools_eq_has_bool_type
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvredand) x =>
      exact congTypeSpine_bvredand_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvredor) x =>
      exact congTypeSpine_bvredor_eq_has_bool_type x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvnot) x =>
      exact congTypeSpine_bv_unop_eq_has_bool_type UserOp.bvnot SmtTerm.bvnot
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_38])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvneg) x =>
      exact congTypeSpine_bv_unop_eq_has_bool_type UserOp.bvneg SmtTerm.bvneg
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_46])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.bvnego) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.bvnego
        SmtTerm.bvnego SmtType.Bool
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_71])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.ubv_to_int) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.ubv_to_int
        SmtTerm.ubv_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_131])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp UserOp.sbv_to_int) x =>
      exact congTypeSpine_bv_unop_ret_eq_has_bool_type UserOp.sbv_to_int
        SmtTerm.sbv_to_int SmtType.Int
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_132])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvand SmtTerm.bvand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_39])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvor SmtTerm.bvor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_40])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvnand SmtTerm.bvnand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_41])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvnor SmtTerm.bvnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_42])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvxor SmtTerm.bvxor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_43])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvxnor SmtTerm.bvxnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_44])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvcomp
        SmtTerm.bvcomp (SmtType.BitVec 1)
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_45])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvadd SmtTerm.bvadd
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_47])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvmul SmtTerm.bvmul
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_48])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvudiv SmtTerm.bvudiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_49])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvurem SmtTerm.bvurem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_50])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsub SmtTerm.bvsub
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_51])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsdiv SmtTerm.bvsdiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_52])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsrem SmtTerm.bvsrem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_53])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvsmod SmtTerm.bvsmod
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_54])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvult
        SmtTerm.bvult SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvule
        SmtTerm.bvule SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvugt
        SmtTerm.bvugt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_57])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvuge
        SmtTerm.bvuge SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_58])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvslt
        SmtTerm.bvslt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsle
        SmtTerm.bvsle SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsgt
        SmtTerm.bvsgt SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_61])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsge
        SmtTerm.bvsge SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_62])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvshl SmtTerm.bvshl
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_63])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvlshr SmtTerm.bvlshr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_64])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) x₁) x₂ =>
      exact congTypeSpine_bv_binop_eq_has_bool_type UserOp.bvashr SmtTerm.bvashr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_65])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.zero_extend i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.zero_extend i
        (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_zero_extend_eq, typeof_zero_extend_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.sign_extend i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.sign_extend i
        (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_sign_extend_eq, typeof_sign_extend_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_left i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.rotate_left i
        (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_rotate_left_eq, typeof_rotate_left_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_right i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.rotate_right i
        (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_rotate_right_eq, typeof_rotate_right_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvuaddo
        SmtTerm.bvuaddo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_70])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsaddo
        SmtTerm.bvsaddo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_72])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvumulo
        SmtTerm.bvumulo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_73])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsmulo
        SmtTerm.bvsmulo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_74])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvusubo
        SmtTerm.bvusubo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_75])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvssubo
        SmtTerm.bvssubo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_76])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x₁) x₂ =>
      exact congTypeSpine_bv_binop_ret_eq_has_bool_type UserOp.bvsdivo
        SmtTerm.bvsdivo SmtType.Bool
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_77])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x₁) x₂ =>
      exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type UserOp.bvultbv
        SmtTerm.bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x₁) x₂ =>
      exact congTypeSpine_bv_pred_to_bv_eq_has_bool_type UserOp.bvsltbv
        SmtTerm.bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        x₁ x₂ rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1._at_bit i) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1._at_bit i
        (bvBitTerm (__eo_to_smt i))
        (by intro a; rfl)
        (by
          intro a b h
          rw [bvBitTerm, bvBitTerm, typeof_eq_eq, typeof_eq_eq,
            typeof_extract_eq,
            typeof_extract_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.int_to_bv w
        (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
        (by intro a; rfl)
        (by
          intro a b h
          rw [typeof_int_to_bv_eq, typeof_int_to_bv_eq, h])
        x rhs hTrans hSpine
  | Term.Apply (Term.UOp1 UserOp1.is c) x =>
      exact congTypeSpine_typecongr_indexed_unop_eq_has_bool_type
        UserOp1.is c
        (fun a => SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) a)
        (by intro a; rfl)
        (by
          intro a b h
          cases __eo_to_smt_tester (__eo_to_smt c) <;>
            simp [__smtx_typeof, h])
        x rhs hTrans hSpine
  | _ =>
      cases hSpine with
      | refl _ =>
          exact congTypeSpine_refl_eq_has_bool_type rhs hTrans
      | app _ _ =>
          sorry

/--
The remaining semantic core for congruence: a syntactic congruence spine
preserves SMT equality in a total typed model.
-/
private theorem congTrueSpine_refl_eq_true
    (M : SmtModel) (t : Term) :
    RuleProofs.eo_has_bool_type (mkEq t t) ->
    eo_interprets M (mkEq t t) true := by
  intro hEqBool
  exact RuleProofs.eo_interprets_eq_of_rel M t t hEqBool
    (RuleProofs.smt_value_rel_refl _)

private theorem congTrueSpine_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t rhs : Term) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    CongTrueSpine M t rhs ->
    eo_interprets M (mkEq t rhs) true := by
  intro hEqBool hSpine
  match t with
  | Term.Apply (Term.UOp UserOp.not) x =>
      exact congTrueSpine_not_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.eq) x₁) x₂ =>
      exact congTrueSpine_eq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e =>
      exact congTrueSpine_ite_eq_true M hM c t e rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e =>
      exact congTrueSpine_bvite_eq_true M hM c t e rhs hEqBool hSpine
  | Term.Apply (Term.Var (Term.String s) T) x =>
      exact congTrueSpine_var_apply_eq_true M hM s T x rhs hEqBool hSpine
  | Term.Apply (Term.UConst i T) x =>
      exact congTrueSpine_uconst_apply_eq_true M hM i T x rhs hEqBool hSpine
  | Term.Apply (Term.DtSel s d i j) x =>
      exact congTrueSpine_dt_sel_eq_true M hM
        s d i j x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂ =>
      exact congTrueSpine_var_apply_apply_eq_true M hM
        s T x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂ =>
      exact congTrueSpine_uconst_apply_apply_eq_true M hM
        i T x₁ x₂ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃ =>
      exact congTrueSpine_var_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃ =>
      exact congTrueSpine_uconst_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
      x₄ =>
      exact congTrueSpine_var_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      x₄ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTrueSpine_var_apply_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ x₅ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        x₄) x₅ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ x₅ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTrueSpine_var_apply_apply_apply_apply_apply_apply_eq_true M hM
        s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hEqBool hSpine
  | Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
          x₄) x₅) x₆ =>
      exact congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_eq_true M hM
        i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂ =>
      exact congTrueSpine_and_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂ =>
      exact congTrueSpine_or_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂ =>
      exact congTrueSpine_imp_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂ =>
      exact congTrueSpine_xor_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂ =>
      exact congTrueSpine_plus_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂ =>
      exact congTrueSpine_neg_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂ =>
      exact congTrueSpine_mult_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂ =>
      exact congTrueSpine_lt_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂ =>
      exact congTrueSpine_leq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂ =>
      exact congTrueSpine_gt_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂ =>
      exact congTrueSpine_geq_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.to_real) x =>
      exact congTrueSpine_to_real_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.to_int) x =>
      exact congTrueSpine_to_int_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.is_int) x =>
      exact congTrueSpine_is_int_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.abs) x =>
      exact congTrueSpine_abs_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.__eoo_neg_2) x =>
      exact congTrueSpine_uneg_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂ =>
      exact congTrueSpine_div_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂ =>
      exact congTrueSpine_mod_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂ =>
      exact congTrueSpine_multmult_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂ =>
      exact congTrueSpine_div_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂ =>
      exact congTrueSpine_mod_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂ =>
      exact congTrueSpine_multmult_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂ =>
      exact congTrueSpine_divisible_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_pow2) x =>
      exact congTrueSpine_int_pow2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_log2) x =>
      exact congTrueSpine_int_log2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.int_ispow2) x =>
      exact congTrueSpine_int_ispow2_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x =>
      exact congTrueSpine_int_div_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_mod_by_zero) x =>
      exact congTrueSpine_mod_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_bvsize) x =>
      exact congTrueSpine_bvsize_eq_true M x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x₁) x₂ =>
      exact congTrueSpine_qdiv_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x₁) x₂ =>
      exact congTrueSpine_qdiv_total_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp._at_div_by_zero) x =>
      exact congTrueSpine_qdiv_by_zero_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_len) x =>
      exact congTrueSpine_seq_unop_ret_eq_true M hM UserOp.str_len
        SmtTerm.str_len SmtType.Int __smtx_model_eval_str_len
        (by intro a; rfl)
        (by intro a; exact typeof_str_len_eq a)
        (by intro a; rw [__smtx_model_eval.eq_79])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_rev) x =>
      exact congTrueSpine_seq_unop_eq_true M hM UserOp.str_rev
        SmtTerm.str_rev __smtx_model_eval_str_rev
        (by intro a; rfl)
        (by intro a; exact typeof_str_rev_eq a)
        (by intro a; rw [__smtx_model_eval.eq_88])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_lower) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_lower SmtTerm.str_to_lower (SmtType.Seq SmtType.Char)
        __smtx_model_eval_str_to_lower
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_lower_eq a)
        (by intro a; rw [__smtx_model_eval.eq_90])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_upper) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_upper SmtTerm.str_to_upper (SmtType.Seq SmtType.Char)
        __smtx_model_eval_str_to_upper
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_upper_eq a)
        (by intro a; rw [__smtx_model_eval.eq_91])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_code) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_code SmtTerm.str_to_code SmtType.Int
        __smtx_model_eval_str_to_code
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_code_eq a)
        (by intro a; rw [__smtx_model_eval.eq_92])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_from_code) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM
        UserOp.str_from_code SmtTerm.str_from_code
        __smtx_model_eval_str_from_code
        (by intro a; rfl)
        (int_ret_unop_args_non_reg_of_non_none SmtTerm.str_from_code
          (SmtType.Seq SmtType.Char)
          (by intro a; exact typeof_str_from_code_eq a))
        (by intro a; rw [__smtx_model_eval.eq_93])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_is_digit) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_is_digit SmtTerm.str_is_digit SmtType.Bool
        __smtx_model_eval_str_is_digit
        (by intro a; rfl)
        (by intro a; exact typeof_str_is_digit_eq a)
        (by intro a; rw [__smtx_model_eval.eq_94])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_int) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_int SmtTerm.str_to_int SmtType.Int
        __smtx_model_eval_str_to_int
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_int_eq a)
        (by intro a; rw [__smtx_model_eval.eq_95])
        x rhs hEqBool hSpine
  | Term._at_strings_stoi_non_digit x =>
      exact congTrueSpine_strings_stoi_non_digit_eq_true M hM
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_from_int) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM
        UserOp.str_from_int SmtTerm.str_from_int
        __smtx_model_eval_str_from_int
        (by intro a; rfl)
        (int_ret_unop_args_non_reg_of_non_none SmtTerm.str_from_int
          (SmtType.Seq SmtType.Char)
          (by intro a; exact typeof_str_from_int_eq a))
        (by intro a; rw [__smtx_model_eval.eq_96])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.str_to_re) x =>
      exact congTrueSpine_seq_char_unop_eq_true M hM
        UserOp.str_to_re SmtTerm.str_to_re SmtType.RegLan
        __smtx_model_eval_str_to_re
        (by intro a; rfl)
        (by intro a; exact typeof_str_to_re_eq a)
        (by intro a; rw [__smtx_model_eval.eq_106])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.re_exp n) x =>
      exact congTrueSpine_re_exp_eq_true M hM n x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_opt) x =>
      exact congTrueSpine_re_opt_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.re_comp) x =>
      exact congTrueSpine_re_comp_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.re_range
        SmtTerm.re_range SmtType.RegLan __smtx_model_eval_re_range
        (by intro a b; rfl)
        (by intro a b; exact typeof_re_range_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_112])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂ =>
      exact congTrueSpine_re_concat_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂ =>
      exact congTrueSpine_re_union_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂ =>
      exact congTrueSpine_re_inter_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂ =>
      exact congTrueSpine_re_diff_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x =>
      exact congTrueSpine_re_loop_eq_true M hM lo hi x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x₁) x₂ =>
      exact congTrueSpine_str_in_re_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.seq_unit) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM UserOp.seq_unit
        SmtTerm.seq_unit
        (fun a =>
          SmtValue.Seq
            (SmtSeq.cons a (SmtSeq.empty (__smtx_typeof_value a))))
        (by intro a; rfl)
        seq_unit_arg_non_reg_of_non_none
        (by intro a; rw [__smtx_model_eval.eq_119])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x₁) x₂ =>
      exact congTrueSpine_seq_binop_eq_true M hM UserOp.str_concat
        SmtTerm.str_concat __smtx_model_eval_str_concat
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_concat_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_80])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x₁) x₂ =>
      exact congTrueSpine_seq_binop_ret_eq_true M hM UserOp.str_contains
        SmtTerm.str_contains SmtType.Bool __smtx_model_eval_str_contains
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_contains_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_82])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x₁) x₂ =>
      exact congTrueSpine_non_reg_binop_eq_true M hM UserOp.str_at
        SmtTerm.str_at __smtx_model_eval_str_at
        (by intro a b; rfl)
        str_at_args_non_reg_of_non_none
        (by intro a b; rw [__smtx_model_eval.eq_85])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_prefixof
        SmtTerm.str_prefixof SmtType.Bool __smtx_model_eval_str_prefixof
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_prefixof_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_86])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_suffixof
        SmtTerm.str_suffixof SmtType.Bool __smtx_model_eval_str_suffixof
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_suffixof_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_87])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_lt
        SmtTerm.str_lt SmtType.Bool __smtx_model_eval_str_lt
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_lt_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_97])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x₁) x₂ =>
      exact congTrueSpine_seq_char_binop_eq_true M hM UserOp.str_leq
        SmtTerm.str_leq SmtType.Bool __smtx_model_eval_str_leq
        (by intro a b; rfl)
        (by intro a b; exact typeof_str_leq_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_98])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x₁) x₂ =>
      exact congTrueSpine_non_reg_binop_eq_true M hM UserOp.seq_nth
        SmtTerm.seq_nth (fun a b => __smtx_seq_nth M a b)
        (by intro a b; rfl)
        seq_nth_args_non_reg_of_non_none
        (by intro a b; rw [__smtx_model_eval.eq_120])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term._at_strings_stoi_result x₁) x₂ =>
      exact congTrueSpine_strings_stoi_result_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term._at_strings_itos_result x₁) x₂ =>
      exact congTrueSpine_strings_itos_result_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂ =>
      exact congTrueSpine_strings_num_occur_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_substr
        SmtTerm.str_substr __smtx_model_eval_str_substr
        (by intro a b c; rfl)
        str_substr_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_81])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_replace
        SmtTerm.str_replace __smtx_model_eval_str_replace
        (by intro a b c; rfl)
        (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace
          (by intro a b c; exact typeof_str_replace_eq a b c))
        (by intro a b c; rw [__smtx_model_eval.eq_83])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_indexof
        SmtTerm.str_indexof __smtx_model_eval_str_indexof
        (by intro a b c; rfl)
        str_indexof_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_84])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM UserOp.str_update
        SmtTerm.str_update __smtx_model_eval_str_update
        (by intro a b c; rfl)
        str_update_args_non_reg_of_non_none
        (by intro a b c; rw [__smtx_model_eval.eq_89])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x₁) x₂) x₃ =>
      exact congTrueSpine_non_reg_ternop_eq_true M hM
        UserOp.str_replace_all SmtTerm.str_replace_all
        __smtx_model_eval_str_replace_all
        (by intro a b c; rfl)
        (seq_triop_args_non_reg_of_non_none SmtTerm.str_replace_all
          (by intro a b c; exact typeof_str_replace_all_eq a b c))
        (by intro a b c; rw [__smtx_model_eval.eq_99])
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂) x₃ =>
      exact congTrueSpine_str_replace_re_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂) x₃ =>
      exact congTrueSpine_str_replace_re_all_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂) x₃ =>
      exact congTrueSpine_str_indexof_re_eq_true M hM
        x₁ x₂ x₃ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.set_is_empty) x =>
      exact congTrueSpine_set_is_empty_eq_true M x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.set_singleton) x =>
      exact congTrueSpine_non_reg_unop_eq_true M hM UserOp.set_singleton
        SmtTerm.set_singleton __smtx_model_eval_set_singleton
        (by intro a; rfl)
        set_singleton_arg_non_reg_of_non_none
        (by intro a; rw [__smtx_model_eval.eq_122])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_union
        SmtTerm.set_union __smtx_model_eval_set_union
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_union_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_123])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_inter
        SmtTerm.set_inter __smtx_model_eval_set_inter
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_inter_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_124])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x₁) x₂ =>
      exact congTrueSpine_set_binop_eq_true M hM UserOp.set_minus
        SmtTerm.set_minus __smtx_model_eval_set_minus
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_minus_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_125])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x₁) x₂ =>
      exact congTrueSpine_set_binop_ret_eq_true M hM UserOp.set_subset
        SmtTerm.set_subset SmtType.Bool __smtx_model_eval_set_subset
        (by intro a b; rfl)
        (by intro a b; exact typeof_set_subset_eq a b)
        (by intro a b; rw [__smtx_model_eval.eq_127])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x₁) x₂ =>
      exact congTrueSpine_bv_concat_eq_true M hM x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp2 UserOp2.extract i j) x =>
      exact congTrueSpine_non_reg_indexed2_unop_eq_true M hM
        UserOp2.extract i j
        (fun a => SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) a)
        (fun a =>
          __smtx_model_eval_extract
            (__smtx_model_eval M (__eo_to_smt i))
            (__smtx_model_eval M (__eo_to_smt j)) a)
        (by intro a; rfl)
        (extract_arg_non_reg_of_non_none (__eo_to_smt i) (__eo_to_smt j))
        (by intro a; rw [__smtx_model_eval.eq_36])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.repeat i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.repeat i
        (fun a => SmtTerm.repeat (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_repeat
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (repeat_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_37])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x₁) x₂ =>
      exact congTrueSpine_bv_from_bools_eq_true M hM
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvredand) x =>
      exact congTrueSpine_bvredand_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvredor) x =>
      exact congTrueSpine_bvredor_eq_true M hM x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1._at_bit i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1._at_bit i
        (bvBitTerm (__eo_to_smt i))
        (fun a =>
          __smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval M (__eo_to_smt i))
              (__smtx_model_eval M (__eo_to_smt i)) a)
            (SmtValue.Binary 1 1))
        (by intro a; rfl)
        (bv_bit_arg_non_reg_of_non_none (__eo_to_smt i))
        (by
          intro a
          rw [bvBitTerm, __smtx_model_eval.eq_134,
            __smtx_model_eval.eq_36, __smtx_model_eval.eq_5])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvnot) x =>
      exact congTrueSpine_bv_unop_eq_true M hM UserOp.bvnot SmtTerm.bvnot
        __smtx_model_eval_bvnot
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_38])
        (by intro a; rw [__smtx_model_eval.eq_38])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvneg) x =>
      exact congTrueSpine_bv_unop_eq_true M hM UserOp.bvneg SmtTerm.bvneg
        __smtx_model_eval_bvneg
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_46])
        (by intro a; rw [__smtx_model_eval.eq_46])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.bvnego) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.bvnego
        SmtTerm.bvnego SmtType.Bool __smtx_model_eval_bvnego
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_71])
        (by intro a; rw [__smtx_model_eval.eq_71])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.ubv_to_int) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.ubv_to_int
        SmtTerm.ubv_to_int SmtType.Int __smtx_model_eval_ubv_to_int
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_131])
        (by intro a; rw [__smtx_model_eval.eq_131])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp UserOp.sbv_to_int) x =>
      exact congTrueSpine_bv_unop_ret_eq_true M hM UserOp.sbv_to_int
        SmtTerm.sbv_to_int SmtType.Int __smtx_model_eval_sbv_to_int
        (by intro a; rfl)
        (by intro a; rw [__smtx_typeof.eq_132])
        (by intro a; rw [__smtx_model_eval.eq_132])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.int_to_bv w) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.int_to_bv w
        (fun a => SmtTerm.int_to_bv (__eo_to_smt w) a)
        (fun a =>
          __smtx_model_eval_int_to_bv
            (__smtx_model_eval M (__eo_to_smt w)) a)
        (by intro a; rfl)
        (int_to_bv_arg_non_reg_of_non_none (__eo_to_smt w))
        (by intro a; rw [__smtx_model_eval.eq_130])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.is c) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.is c
        (fun a => SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) a)
        (fun a =>
          match __eo_to_smt_tester (__eo_to_smt c) with
          | SmtTerm.DtTester s d i => __smtx_model_eval_dt_tester s d i a
          | tester => __smtx_model_eval_apply M (__smtx_model_eval M tester) a)
        (by intro a; rfl)
        (is_arg_non_reg_of_non_none c)
        (by
          intro a
          cases __eo_to_smt c <;>
            simp [__eo_to_smt_tester, __smtx_model_eval])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvand SmtTerm.bvand
        __smtx_model_eval_bvand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_39])
        (by intro a b; rw [__smtx_model_eval.eq_39])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvor SmtTerm.bvor
        __smtx_model_eval_bvor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_40])
        (by intro a b; rw [__smtx_model_eval.eq_40])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvnand SmtTerm.bvnand
        __smtx_model_eval_bvnand
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_41])
        (by intro a b; rw [__smtx_model_eval.eq_41])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvnor SmtTerm.bvnor
        __smtx_model_eval_bvnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_42])
        (by intro a b; rw [__smtx_model_eval.eq_42])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvxor SmtTerm.bvxor
        __smtx_model_eval_bvxor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_43])
        (by intro a b; rw [__smtx_model_eval.eq_43])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvxnor SmtTerm.bvxnor
        __smtx_model_eval_bvxnor
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_44])
        (by intro a b; rw [__smtx_model_eval.eq_44])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvcomp
        SmtTerm.bvcomp (SmtType.BitVec 1) __smtx_model_eval_bvcomp
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_45])
        (by intro a b; rw [__smtx_model_eval.eq_45])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvadd SmtTerm.bvadd
        __smtx_model_eval_bvadd
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_47])
        (by intro a b; rw [__smtx_model_eval.eq_47])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvmul SmtTerm.bvmul
        __smtx_model_eval_bvmul
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_48])
        (by intro a b; rw [__smtx_model_eval.eq_48])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvudiv SmtTerm.bvudiv
        __smtx_model_eval_bvudiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_49])
        (by intro a b; rw [__smtx_model_eval.eq_49])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvurem SmtTerm.bvurem
        __smtx_model_eval_bvurem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_50])
        (by intro a b; rw [__smtx_model_eval.eq_50])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsub SmtTerm.bvsub
        __smtx_model_eval_bvsub
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_51])
        (by intro a b; rw [__smtx_model_eval.eq_51])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsdiv SmtTerm.bvsdiv
        __smtx_model_eval_bvsdiv
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_52])
        (by intro a b; rw [__smtx_model_eval.eq_52])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsrem SmtTerm.bvsrem
        __smtx_model_eval_bvsrem
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_53])
        (by intro a b; rw [__smtx_model_eval.eq_53])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvsmod SmtTerm.bvsmod
        __smtx_model_eval_bvsmod
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_54])
        (by intro a b; rw [__smtx_model_eval.eq_54])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvult
        SmtTerm.bvult SmtType.Bool __smtx_model_eval_bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        (by intro a b; rw [__smtx_model_eval.eq_55])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvule
        SmtTerm.bvule SmtType.Bool __smtx_model_eval_bvule
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_56])
        (by intro a b; rw [__smtx_model_eval.eq_56])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvugt
        SmtTerm.bvugt SmtType.Bool __smtx_model_eval_bvugt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_57])
        (by intro a b; rw [__smtx_model_eval.eq_57])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvuge
        SmtTerm.bvuge SmtType.Bool __smtx_model_eval_bvuge
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_58])
        (by intro a b; rw [__smtx_model_eval.eq_58])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvslt
        SmtTerm.bvslt SmtType.Bool __smtx_model_eval_bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        (by intro a b; rw [__smtx_model_eval.eq_59])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsle
        SmtTerm.bvsle SmtType.Bool __smtx_model_eval_bvsle
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_60])
        (by intro a b; rw [__smtx_model_eval.eq_60])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsgt
        SmtTerm.bvsgt SmtType.Bool __smtx_model_eval_bvsgt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_61])
        (by intro a b; rw [__smtx_model_eval.eq_61])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsge
        SmtTerm.bvsge SmtType.Bool __smtx_model_eval_bvsge
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_62])
        (by intro a b; rw [__smtx_model_eval.eq_62])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvshl SmtTerm.bvshl
        __smtx_model_eval_bvshl
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_63])
        (by intro a b; rw [__smtx_model_eval.eq_63])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvlshr SmtTerm.bvlshr
        __smtx_model_eval_bvlshr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_64])
        (by intro a b; rw [__smtx_model_eval.eq_64])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) x₁) x₂ =>
      exact congTrueSpine_bv_binop_eq_true M hM UserOp.bvashr SmtTerm.bvashr
        __smtx_model_eval_bvashr
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_65])
        (by intro a b; rw [__smtx_model_eval.eq_65])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.zero_extend i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.zero_extend i
        (fun a => SmtTerm.zero_extend (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_zero_extend
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (zero_extend_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_66])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.sign_extend i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.sign_extend i
        (fun a => SmtTerm.sign_extend (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_sign_extend
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (sign_extend_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_67])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_left i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.rotate_left i
        (fun a => SmtTerm.rotate_left (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_rotate_left
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (rotate_left_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_68])
        x rhs hEqBool hSpine
  | Term.Apply (Term.UOp1 UserOp1.rotate_right i) x =>
      exact congTrueSpine_non_reg_indexed_unop_eq_true M hM
        UserOp1.rotate_right i
        (fun a => SmtTerm.rotate_right (__eo_to_smt i) a)
        (fun a =>
          __smtx_model_eval_rotate_right
            (__smtx_model_eval M (__eo_to_smt i)) a)
        (by intro a; rfl)
        (rotate_right_arg_non_reg_of_non_none (__eo_to_smt i))
        (by intro a; rw [__smtx_model_eval.eq_69])
        x rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvuaddo
        SmtTerm.bvuaddo SmtType.Bool __smtx_model_eval_bvuaddo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_70])
        (by intro a b; rw [__smtx_model_eval.eq_70])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsaddo
        SmtTerm.bvsaddo SmtType.Bool __smtx_model_eval_bvsaddo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_72])
        (by intro a b; rw [__smtx_model_eval.eq_72])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvumulo
        SmtTerm.bvumulo SmtType.Bool __smtx_model_eval_bvumulo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_73])
        (by intro a b; rw [__smtx_model_eval.eq_73])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsmulo
        SmtTerm.bvsmulo SmtType.Bool __smtx_model_eval_bvsmulo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_74])
        (by intro a b; rw [__smtx_model_eval.eq_74])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvusubo
        SmtTerm.bvusubo SmtType.Bool __smtx_model_eval_bvusubo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_75])
        (by intro a b; rw [__smtx_model_eval.eq_75])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvssubo
        SmtTerm.bvssubo SmtType.Bool __smtx_model_eval_bvssubo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_76])
        (by intro a b; rw [__smtx_model_eval.eq_76])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x₁) x₂ =>
      exact congTrueSpine_bv_binop_ret_eq_true M hM UserOp.bvsdivo
        SmtTerm.bvsdivo SmtType.Bool __smtx_model_eval_bvsdivo
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_77])
        (by intro a b; rw [__smtx_model_eval.eq_77])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x₁) x₂ =>
      exact congTrueSpine_bv_pred_to_bv_eq_true M hM UserOp.bvultbv
        SmtTerm.bvult __smtx_model_eval_bvult
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_55])
        (by
          intro a b
          rw [bvPredToBv, bvPredToBvEval, __smtx_model_eval.eq_133,
            __smtx_model_eval.eq_55, __smtx_model_eval.eq_5,
            __smtx_model_eval.eq_5])
        x₁ x₂ rhs hEqBool hSpine
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x₁) x₂ =>
      exact congTrueSpine_bv_pred_to_bv_eq_true M hM UserOp.bvsltbv
        SmtTerm.bvslt __smtx_model_eval_bvslt
        (by intro a b; rfl)
        (by intro a b; rw [__smtx_typeof.eq_59])
        (by
          intro a b
          rw [bvPredToBv, bvPredToBvEval, __smtx_model_eval.eq_133,
            __smtx_model_eval.eq_59, __smtx_model_eval.eq_5,
            __smtx_model_eval.eq_5])
        x₁ x₂ rhs hEqBool hSpine
  | _ =>
      cases hSpine with
      | refl _ =>
          exact congTrueSpine_refl_eq_true M rhs hEqBool
      | app _ _ =>
          sorry

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
      (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply M (__smtx_model_eval M g) (__smtx_model_eval M y)) :=
  smt_value_rel_model_eval_apply_of_rel_core M hM f g x y
    hAppNN hFy hXy hFRel hXRel

end CongSupport
