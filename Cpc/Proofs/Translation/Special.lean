import Cpc.Proofs.Translation.EoTypeof
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.TypePreservationFull

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace TranslationProofs

private theorem map_diff_left_non_none_of_non_none
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.map_diff x y) ≠ SmtType.None ->
      __smtx_typeof x ≠ SmtType.None := by
  intro h
  cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
      simp [__smtx_typeof, __smtx_typeof_map_diff, hx, hy, native_ite, native_Teq,
        SmtEval.native_and] at h ⊢

private theorem map_diff_right_non_none_of_non_none
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.map_diff x y) ≠ SmtType.None ->
      __smtx_typeof y ≠ SmtType.None := by
  intro h
  cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
      simp [__smtx_typeof, __smtx_typeof_map_diff, hx, hy, native_ite, native_Teq,
        SmtEval.native_and] at h ⊢

private theorem eo_to_smt_type_ne_none_term_ne_stuck (t : Term) :
    __eo_to_smt_type t ≠ SmtType.None ->
      t ≠ Term.Stuck := by
  intro h ht
  subst ht
  simp [__eo_to_smt_type] at h

private theorem eq_of_eo_eq_true (x y : Term)
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

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
      y = x := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  exact eq_of_eo_eq_true x y hProg'.1

private theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
      x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true :=
    hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧
        __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq, ha, hb]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

private theorem eqs_of_eo_and_eo_eq_true (x1 y1 x2 y2 : Term)
    (hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true) :
    x2 = x1 ∧ y2 = y1 := by
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧
        __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq, ha, hb]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;>
      simp [__eo_and, hX, hY, SmtEval.native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

private def eo_eq_unfolded_for_proof : Term -> Term -> Term
  | Term.Stuck, _ => Term.Stuck
  | _, Term.Stuck => Term.Stuck
  | t, s => Term.Boolean (decide (s = t))

private def eo_and_unfolded_for_proof : Term -> Term -> Term
  | Term.Boolean b1, Term.Boolean b2 => Term.Boolean (b1 && b2)
  | Term.Binary w1 n1, Term.Binary w2 n2 =>
    if w1 = w2 then
      if native_not false = true then
        Term.Binary w2
          (native_mod_total (native_binary_and w2 n1 n2) (native_int_pow2 w2))
      else Term.Stuck
    else Term.Stuck
  | _, _ => Term.Stuck

private theorem eo_and_eq_true_of_unfolded_eq_true (p q : Term)
    (h : eo_and_unfolded_for_proof p q = Term.Boolean true) :
    __eo_and p q = Term.Boolean true := by
  cases p <;> cases q <;>
    try simp [eo_and_unfolded_for_proof, __eo_and, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not, SmtEval.native_and] at h ⊢ <;> try assumption
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;>
      simp [eo_and_unfolded_for_proof, __eo_and, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hw] at h

private theorem eo_eq_true_of_unfolded_eq_true (x y : Term)
    (h : eo_eq_unfolded_for_proof x y = Term.Boolean true) :
    __eo_eq x y = Term.Boolean true := by
  cases x <;> cases y <;>
    simp [eo_eq_unfolded_for_proof, __eo_eq, native_teq] at h ⊢ <;> try assumption

private theorem eq_of_requires_eq_true_type_ne_none (x y B : Term) :
    __eo_to_smt_type (__eo_requires (__eo_eq x y) (Term.Boolean true) B) ≠
      SmtType.None ->
      y = x := by
  intro h
  apply eq_of_requires_eq_true_not_stuck x y B
  exact eo_to_smt_type_ne_none_term_ne_stuck _ h

private theorem eqs_of_requires_and_eq_true_type_ne_none (x1 y1 x2 y2 B : Term) :
    __eo_to_smt_type
        (__eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
          (Term.Boolean true) B) ≠ SmtType.None ->
      x2 = x1 ∧ y2 = y1 := by
  intro h
  apply eqs_of_requires_and_eq_true_not_stuck x1 y1 x2 y2 B
  exact eo_to_smt_type_ne_none_term_ne_stuck _ h

private theorem requires_and_eq_self_eq_of_not_stuck (x y : Term) :
    __eo_requires (__eo_and (__eo_eq x x) (__eo_eq y y))
      (Term.Boolean true) x ≠ Term.Stuck ->
    __eo_requires (__eo_and (__eo_eq x x) (__eo_eq y y))
      (Term.Boolean true) x = x := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not, SmtEval.native_and] at h ⊢

private theorem requires_eq_self_eq_of_not_stuck (x : Term) :
    __eo_requires (__eo_eq x x) (Term.Boolean true) x ≠ Term.Stuck ->
    __eo_requires (__eo_eq x x) (Term.Boolean true) x = x := by
  intro h
  cases x <;>
    simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not] at h ⊢

private theorem map_diff_typeof_same_array_type (T U : Term)
    (h :
      __smtx_typeof_map_diff
          (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U))
          (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U)) ≠
        SmtType.None) :
    __smtx_typeof_map_diff
        (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U))
        (__eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U)) =
      __eo_to_smt_type T := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [__eo_to_smt_type, __smtx_typeof_map_diff, __smtx_typeof_guard,
      native_ite, native_Teq, SmtEval.native_and, hT, hU] at h ⊢

private theorem map_diff_typeof_same_set_type (T : Term)
    (h :
      __smtx_typeof_map_diff
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T))
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) ≠
        SmtType.None) :
    __smtx_typeof_map_diff
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T)) =
      __eo_to_smt_type T := by
  cases hT : __eo_to_smt_type T <;>
    simp [__eo_to_smt_type, __smtx_typeof_map_diff, __smtx_typeof_guard,
      native_ite, native_Teq, SmtEval.native_and, hT] at h ⊢

private theorem map_diff_typeof_eo_array_deq_diff
    (T U : Term)
    (hDiffNN :
      __smtx_typeof_map_diff (__eo_to_smt_type T) (__eo_to_smt_type U) ≠
        SmtType.None)
    (hRetNN :
      __eo_to_smt_type (__eo_typeof__at_array_deq_diff T U) ≠ SmtType.None) :
    __smtx_typeof_map_diff (__eo_to_smt_type T) (__eo_to_smt_type U) =
      __eo_to_smt_type (__eo_typeof__at_array_deq_diff T U) := by
  cases T <;> simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
    __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
  case Apply f a =>
    cases f <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
      __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
      __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
    case Apply g b =>
      cases g <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
        __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
      case UOp op =>
        cases op <;> simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
          __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
          __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
        case Array =>
          cases U <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
            __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
            __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
          case Apply f2 a2 =>
            cases f2 <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
              __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
              __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
            case Apply g2 b2 =>
              cases g2 <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
                __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
                __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
              case UOp op2 =>
                cases op2 <;> try simp_all [__eo_typeof__at_array_deq_diff, __eo_to_smt_type,
                  __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_and,
                  __eo_eq, native_ite, native_teq, native_Teq, SmtEval.native_and]
                case Array =>
                  by_cases hCond :
                      eo_and_unfolded_for_proof
                        (eo_eq_unfolded_for_proof b b2)
                        (eo_eq_unfolded_for_proof a a2) = Term.Boolean true
                  · have hAnd :
                        __eo_and (__eo_eq b b2) (__eo_eq a a2) = Term.Boolean true :=
                      eo_and_eq_true_of_unfolded_eq_true (__eo_eq b b2) (__eo_eq a a2)
                        (by simpa [eo_and_unfolded_for_proof, eo_eq_unfolded_for_proof,
                          __eo_eq] using hCond)
                    rcases eqs_of_eo_and_eo_eq_true b a b2 a2 hAnd with ⟨hb, ha⟩
                    subst b2
                    subst a2
                    change _ =
                      __eo_to_smt_type
                        (if
                          eo_and_unfolded_for_proof
                            (eo_eq_unfolded_for_proof b b)
                            (eo_eq_unfolded_for_proof a a) = Term.Boolean true
                         then b else Term.Stuck)
                    rw [if_pos hCond]
                    cases hbTy : __eo_to_smt_type b <;>
                      cases haTy : __eo_to_smt_type a <;>
                        simp [__eo_to_smt_type, __smtx_typeof_map_diff,
                          __smtx_typeof_guard, native_ite, native_Teq,
                          SmtEval.native_and, hbTy, haTy] at hDiffNN hRetNN ⊢
                  · exfalso
                    apply hRetNN
                    change __eo_to_smt_type
                        (if
                          eo_and_unfolded_for_proof
                            (eo_eq_unfolded_for_proof b b2)
                            (eo_eq_unfolded_for_proof a a2) = Term.Boolean true
                         then b else Term.Stuck) = SmtType.None
                    rw [if_neg hCond]
                    rfl

private theorem map_diff_typeof_eo_sets_deq_diff
    (T U : Term)
    (hDiffNN :
      __smtx_typeof_map_diff (__eo_to_smt_type T) (__eo_to_smt_type U) ≠
        SmtType.None)
    (hRetNN :
      __eo_to_smt_type (__eo_typeof__at_sets_deq_diff T U) ≠ SmtType.None) :
    __smtx_typeof_map_diff (__eo_to_smt_type T) (__eo_to_smt_type U) =
      __eo_to_smt_type (__eo_typeof__at_sets_deq_diff T U) := by
  cases T <;> simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
    __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
    native_ite, native_teq, native_Teq, SmtEval.native_and]
  case Apply f a =>
    cases f <;> try simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
      __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
      native_ite, native_teq, native_Teq, SmtEval.native_and]
    case UOp op =>
      cases op <;> simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
        __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
        native_ite, native_teq, native_Teq, SmtEval.native_and]
      case Set =>
        cases U <;> try simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
          __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
          native_ite, native_teq, native_Teq, SmtEval.native_and]
        case Apply f2 a2 =>
          cases f2 <;> try simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
            __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
            native_ite, native_teq, native_Teq, SmtEval.native_and]
          case UOp op2 =>
            cases op2 <;> try simp_all [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type,
              __smtx_typeof_map_diff, __smtx_typeof_guard, __eo_requires, __eo_eq,
              native_ite, native_teq, native_Teq, SmtEval.native_and]
            case Set =>
              by_cases hCond :
                  eo_eq_unfolded_for_proof a a2 = Term.Boolean true
              · have hEq : __eo_eq a a2 = Term.Boolean true :=
                  eo_eq_true_of_unfolded_eq_true a a2 hCond
                have ha := eq_of_eo_eq_true a a2 hEq
                subst a2
                change _ =
                  __eo_to_smt_type
                    (if eo_eq_unfolded_for_proof a a = Term.Boolean true
                     then a else Term.Stuck)
                rw [if_pos hCond]
                cases hTy : __eo_to_smt_type a <;>
                  simp [__eo_to_smt_type, __smtx_typeof_map_diff,
                    __smtx_typeof_guard, native_ite, native_Teq,
                    SmtEval.native_and, hTy] at hDiffNN hRetNN ⊢
              · exfalso
                apply hRetNN
                change __eo_to_smt_type
                    (if eo_eq_unfolded_for_proof a a2 = Term.Boolean true
                     then a else Term.Stuck) = SmtType.None
                rw [if_neg hCond]
                rfl


/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_purify`. -/
theorem eo_to_smt_typeof_matches_translation_purify
    (x : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof (Term._at_purify x)) := by
  change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) =
    __eo_to_smt_type (__eo_typeof (Term._at_purify x))
  simp [__smtx_typeof]
  rw [hx]
  exact (eo_to_smt_type_typeof_purify x).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_array_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_array_deq_diff
    (x1 x2 : Term)
    (ih1 :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  intro hNonNone
  let T := __eo_to_smt_type (__eo_typeof (Term.UOp2 UserOp2._at_array_deq_diff x1 x2))
  change
    __smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_array_deq_diff x1 x2)) ≠
      SmtType.None at hNonNone
  change
    __smtx_typeof
        (native_ite (native_Teq T SmtType.None) SmtTerm.None
          (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  have hTFalse : native_Teq T SmtType.None = false := by
    cases hT : native_Teq T SmtType.None
    · rfl
    · exfalso
      apply hNonNone
      simp [native_ite, hT]
  have hMapNN :
      __smtx_typeof (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) ≠
        SmtType.None := by
    simpa [native_ite, hTFalse] using hNonNone
  have hx1 := ih1 (map_diff_left_non_none_of_non_none _ _ hMapNN)
  have hx2 := ih2 (map_diff_right_non_none_of_non_none _ _ hMapNN)
  change
    __smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term.UOp2 UserOp2._at_array_deq_diff x1 x2))
  change
    __smtx_typeof
        (native_ite (native_Teq T SmtType.None) SmtTerm.None
          (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
      T
  rw [hTFalse]
  change __smtx_typeof (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) = T
  simp [__smtx_typeof]
  rw [hx1, hx2]
  apply map_diff_typeof_eo_array_deq_diff
  · simpa [__smtx_typeof, hx1, hx2] using hMapNN
  · change T ≠ SmtType.None
    simpa [native_Teq] using hTFalse

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_sets_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_sets_deq_diff
    (x1 x2 : Term)
    (ih1 :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  intro hNonNone
  let T := __eo_to_smt_type (__eo_typeof (Term.UOp2 UserOp2._at_sets_deq_diff x1 x2))
  change
    __smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_sets_deq_diff x1 x2)) ≠
      SmtType.None at hNonNone
  change
    __smtx_typeof
        (native_ite (native_Teq T SmtType.None) SmtTerm.None
          (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  have hTFalse : native_Teq T SmtType.None = false := by
    cases hT : native_Teq T SmtType.None
    · rfl
    · exfalso
      apply hNonNone
      simp [native_ite, hT]
  have hMapNN :
      __smtx_typeof (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) ≠
        SmtType.None := by
    simpa [native_ite, hTFalse] using hNonNone
  have hx1 := ih1 (map_diff_left_non_none_of_non_none _ _ hMapNN)
  have hx2 := ih2 (map_diff_right_non_none_of_non_none _ _ hMapNN)
  change
    __smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term.UOp2 UserOp2._at_sets_deq_diff x1 x2))
  change
    __smtx_typeof
        (native_ite (native_Teq T SmtType.None) SmtTerm.None
          (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
      T
  rw [hTFalse]
  change __smtx_typeof (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) = T
  simp [__smtx_typeof]
  rw [hx1, hx2]
  apply map_diff_typeof_eo_sets_deq_diff
  · simpa [__smtx_typeof, hx1, hx2] using hMapNN
  · change T ≠ SmtType.None
    simpa [native_Teq] using hTFalse

end TranslationProofs
