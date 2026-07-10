import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrConcatClashSupport

/-!
Equal sequence concatenations with equally long prefixes have equal prefixes.
These are local support lemmas for the CPC string-clash rewrites.
-/

theorem smt_seq_rel_pack_prefix_of_eq_length (T : SmtType) :
    ∀ xs ys xs' ys' : List SmtValue,
      xs.length = ys.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ xs'))
        (native_pack_seq T (ys ++ ys')) ->
      RuleProofs.smt_seq_rel (native_pack_seq T xs)
        (native_pack_seq T ys)
  | [], [], xs', ys', _hLen, _hRel => by
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 rfl
  | [], _ :: _, xs', ys', hLen, _hRel => by
      cases hLen
  | _ :: _, [], xs', ys', hLen, _hRel => by
      cases hLen
  | x :: xs, y :: ys, xs', ys', hLen, hRel => by
      have hTailLen : xs.length = ys.length := by
        simpa using Nat.succ.inj hLen
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq] at hRel ⊢
      have hTailRel :=
        smt_seq_rel_pack_prefix_of_eq_length T xs ys xs' ys' hTailLen
          ((RuleProofs.smt_seq_rel_iff_eq _ _).2 hRel.2)
      exact ⟨hRel.1, (RuleProofs.smt_seq_rel_iff_eq _ _).1 hTailRel⟩

theorem smt_value_rel_str_concat_heads_of_eq_length
    (M : SmtModel) (hM : model_total_typed M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq,
    smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hxsEval, hyEval, hysEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxs)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxs))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  have hHeadPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) (native_unpack_seq sxs)
      (native_unpack_seq sys) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

theorem smt_value_rel_str_concat_head_of_eq_length
    (M : SmtModel) (hM : model_total_typed M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel
  rw [smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hysEval] at hRel
  change RuleProofs.smt_seq_rel sx
    (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  rw [hsyElem] at hRel
  have hPackedRel : RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ []))
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) := by
    simpa using RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx)) sx
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys))
      (RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq T (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack T sx hsxElem)) hRel
  have hHeadPack : RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) [] (native_unpack_seq sys) hLenXY hPackedRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

abbrev concatClashNePremise (x y : Term) : Term :=
  mkEq (mkEq x y) (Term.Boolean false)

abbrev concatClashLenPremise (x y : Term) : Term :=
  mkEq (mkStrLen x) (mkStrLen y)

abbrev concatClashConclusion (x xs y ys : Term) : Term :=
  mkEq (mkEq (mkConcat x xs) (mkConcat y ys)) (Term.Boolean false)

abbrev concatClash2Conclusion (x y ys : Term) : Term :=
  mkEq (mkEq x (mkConcat y ys)) (Term.Boolean false)

theorem eo_typeof_str_concat_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_concat A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_concat] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_concat] at h ⊢
            case Seq =>
              have hEq := RuleProofs.eq_of_requires_eq_true_not_stuck
                x y (Term.Apply Term.Seq x) h
              subst y
              simp

theorem smtx_typeof_seq_of_eo_typeof
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

theorem concat_clash_eo_and_true_split (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    simp_all [__eo_and, native_and, SmtEval.native_and]
  all_goals
    simp only [__eo_requires, native_ite, native_teq] at h
  all_goals
    split at h <;> exact Term.noConfusion h

theorem concat_clash_requires_guard_eq (x y z : Term)
    (h : __eo_requires x y z ≠ Term.Stuck) : x = y := by
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

theorem concat_clash_smt_seq_types_of_eo_type
    (x xs y ys : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hxsTrans : RuleProofs.eo_has_smt_translation xs)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hysTrans : RuleProofs.eo_has_smt_translation ys)
    (hTy : __eo_typeof (concatClashConclusion x xs y ys) = Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T := by
  change __eo_typeof_eq
      (__eo_typeof (mkEq (mkConcat x xs) (mkConcat y ys))) Term.Bool =
    Term.Bool at hTy
  have hInnerTy :
      __eo_typeof (mkEq (mkConcat x xs) (mkConcat y ys)) = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof (mkConcat x xs))
    (__eo_typeof (mkConcat y ys)) = Term.Bool at hInnerTy
  have hConcatSame :
      __eo_typeof (mkConcat x xs) = __eo_typeof (mkConcat y ys) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hInnerTy
  have hConcatNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInnerTy
  have hLeftNe := hConcatNe.1
  have hRightNe := hConcatNe.2
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof xs) ≠
    Term.Stuck at hLeftNe
  change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) ≠
    Term.Stuck at hRightNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hLeftNe with
    ⟨U, hxEo, hxsEo⟩
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hRightNe with
    ⟨V, hyEo, hysEo⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hxEo, hxsEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hLeftNe
  have hVNe : V ≠ Term.Stuck := by
    intro hV
    subst V
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hRightNe
  have hLeftEo : __eo_typeof (mkConcat x xs) = Term.Apply Term.Seq U := by
    change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof xs) = _
    simp [hxEo, hxsEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hUNe]
  have hRightEo : __eo_typeof (mkConcat y ys) = Term.Apply Term.Seq V := by
    change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) = _
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hVNe]
  have hUV : U = V := by
    rw [hLeftEo, hRightEo] at hConcatSame
    injection hConcatSame
  subst V
  refine ⟨__eo_to_smt_type U,
    smtx_typeof_seq_of_eo_typeof x U hxTrans hxEo,
    smtx_typeof_seq_of_eo_typeof xs U hxsTrans hxsEo,
    smtx_typeof_seq_of_eo_typeof y U hyTrans hyEo,
    smtx_typeof_seq_of_eo_typeof ys U hysTrans hysEo⟩

theorem concat_clash2_smt_seq_types_of_eo_type
    (x y ys : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x)
    (hyTrans : RuleProofs.eo_has_smt_translation y)
    (hysTrans : RuleProofs.eo_has_smt_translation ys)
    (hTy : __eo_typeof (concatClash2Conclusion x y ys) = Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T := by
  change __eo_typeof_eq (__eo_typeof (mkEq x (mkConcat y ys))) Term.Bool =
    Term.Bool at hTy
  have hInnerTy : __eo_typeof (mkEq x (mkConcat y ys)) = Term.Bool :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof (mkConcat y ys)) =
    Term.Bool at hInnerTy
  have hSame : __eo_typeof x = __eo_typeof (mkConcat y ys) :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hInnerTy
  have hRightNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hInnerTy).2
  change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) ≠
    Term.Stuck at hRightNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hRightNe with
    ⟨U, hyEo, hysEo⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hRightNe
  have hRightEo : __eo_typeof (mkConcat y ys) = Term.Apply Term.Seq U := by
    change __eo_typeof_str_concat (__eo_typeof y) (__eo_typeof ys) = _
    simp [hyEo, hysEo, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not, hUNe]
  have hxEo : __eo_typeof x = Term.Apply Term.Seq U := by
    rw [hSame, hRightEo]
  refine ⟨__eo_to_smt_type U,
    smtx_typeof_seq_of_eo_typeof x U hxTrans hxEo,
    smtx_typeof_seq_of_eo_typeof y U hyTrans hyEo,
    smtx_typeof_seq_of_eo_typeof ys U hysTrans hysEo⟩

theorem smtx_model_eval_eq_false_of_not_rel (v w : SmtValue)
    (h : ¬ RuleProofs.smt_value_rel v w) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v w) with
    ⟨b, hb⟩
  cases b with
  | false => exact hb
  | true =>
      exfalso
      apply h
      exact hb

theorem str_len_eq_unpack_length_eq
    (M : SmtModel) (x y : Term)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    ∀ sx sy : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
  intro sx sy hxEval hyEval
  have hLenRel := RuleProofs.eo_interprets_eq_rel M
    (mkStrLen x) (mkStrLen y) hLen
  change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt x)))
      (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt y))) at hLenRel
  rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
    hxEval, hyEval] at hLenRel
  unfold RuleProofs.smt_value_rel at hLenRel
  have hLenInt :
      ((native_unpack_seq sx).length : Int) =
        ((native_unpack_seq sy).length : Int) := by
    simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
      native_seq_len, native_veq] using hLenRel
  exact_mod_cast hLenInt

theorem eo_has_bool_type_concat_clash
    (x xs y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClashConclusion x xs y ys) := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x xs)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x xs T hxTy hxsTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y ys)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y ys T hyTy hysTy
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x xs) (mkConcat y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; exact seq_ne_none T)
  have hFalseBool :
      RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem eo_has_bool_type_concat_clash2
    (x y ys : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (concatClash2Conclusion x y ys) := by
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y ys)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y ys T hyTy hysTy
  have hInnerBool : RuleProofs.eo_has_bool_type
      (mkEq x (mkConcat y ys)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hxTy, hRightTy]) (by rw [hxTy]; exact seq_ne_none T)
  have hFalseBool :
      RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hInnerBool.trans hFalseBool.symm)
    (by rw [hInnerBool]; decide)

theorem concat_clash_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) := by
    intro hConcatRel
    have hHeadRel := smt_value_rel_str_concat_heads_of_eq_length
      M hM x xs y ys T hxTy hxsTy hyTy hysTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hHeadRel
    rw [hHeadFalse] at hHeadRel
    cases hHeadRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem concat_clash2_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    __smtx_model_eval_eq
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false := by
  have hHeadFalse :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M x y hNe
  have hNotRel : ¬ RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) := by
    intro hConcatRel
    have hHeadRel := smt_value_rel_str_concat_head_of_eq_length
      M hM x y ys T hxTy hyTy hysTy
      (str_len_eq_unpack_length_eq M x y hLen) hConcatRel
    unfold RuleProofs.smt_value_rel at hHeadRel
    rw [hHeadFalse] at hHeadRel
    cases hHeadRel
  exact smtx_model_eval_eq_false_of_not_rel _ _ hNotRel

theorem eo_interprets_concat_clash
    (M : SmtModel) (hM : model_total_typed M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClashConclusion x xs y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash x xs y ys T hxTy hxsTy hyTy hysTy
  · have hInnerEval :
        __smtx_model_eval M
            (__eo_to_smt (mkEq (mkConcat x xs) (mkConcat y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt (mkConcat x xs))
            (__eo_to_smt (mkConcat y ys))) = SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash_model_eval_eq_false M hM x xs y ys T
        hxTy hxsTy hyTy hysTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

theorem eo_interprets_concat_clash2
    (M : SmtModel) (hM : model_total_typed M) (x y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hNe : eo_interprets M (concatClashNePremise x y) true)
    (hLen : eo_interprets M (concatClashLenPremise x y) true) :
    eo_interprets M (concatClash2Conclusion x y ys) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact eo_has_bool_type_concat_clash2 x y ys T hxTy hyTy hysTy
  · have hInnerEval :
        __smtx_model_eval M (__eo_to_smt (mkEq x (mkConcat y ys))) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt (mkConcat y ys))) =
        SmtValue.Boolean false
      rw [smtx_eval_eq_term_eq]
      exact concat_clash2_model_eval_eq_false M hM x y ys T
        hxTy hyTy hysTy hNe hLen
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false
      rw [__smtx_model_eval.eq_def]
    rw [hInnerEval, hFalseEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

end StrConcatClashSupport
