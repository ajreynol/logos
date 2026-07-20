module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterCstringProof

abbrev reInter (x ys : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) ys

abbrev lhs (x ys s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_inter)
      (Term.Apply (Term.UOp UserOp.str_to_re) s))
    (reInter x ys)

private abbrev rhs (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

private abbrev prem (s x ys : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (lhs x ys s)))
    (Term.Boolean true)

private abbrev concl (x ys s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs x ys s)) (rhs s)

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

theorem eo_and_eq_true {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  unfold __eo_and at h
  split at h
  · rename_i b1 b2
    simp only [Term.Boolean.injEq, SmtEval.native_and, Bool.and_eq_true] at h
    exact ⟨by rw [h.1], by rw [h.2]⟩
  · rename_i w1 n1 w2 n2
    simp only [__eo_requires, native_ite] at h
    split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem eqs_of_eo_and4_eq_true
    (x1 y1 x2 y2 x3 y3 x4 y4 : Term)
    (h :
      __eo_and
          (__eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  rcases eo_and_eq_true h with ⟨h123, h4⟩
  rcases eo_and_eq_true h123 with ⟨h12, h3⟩
  rcases eo_and_eq_true h12 with ⟨h1, h2⟩
  exact ⟨eo_eq_eq_true h1, eo_eq_eq_true h2, eo_eq_eq_true h3,
    eo_eq_eq_true h4⟩

theorem eo_typeof_re_concat_ne_stuck_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  cases A with
  | UOp opA =>
      cases opA <;> cases B with
      | UOp opB => cases opB <;> simp [__eo_typeof_re_concat] at h ⊢
      | _ => simp [__eo_typeof_re_concat] at h
  | _ => cases B <;> simp [__eo_typeof_re_concat] at h

theorem eo_typeof_re_concat_eq_reglan_args_reglan (A B : Term)
    (h : __eo_typeof_re_concat A B = Term.UOp UserOp.RegLan) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  exact eo_typeof_re_concat_ne_stuck_args_reglan A B (by rw [h]; simp)

theorem eo_typeof_str_to_re_eq_seq_char_of_reglan (T : Term)
    (h : __eo_typeof_str_to_re T = Term.UOp UserOp.RegLan) :
    T = Term.Apply Term.Seq Term.Char := by
  have hNe : __eo_typeof_str_to_re T ≠ Term.Stuck := by
    rw [h]
    simp
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_to_re] at hNe ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_to_re] at hNe ⊢
            | _ => simp [__eo_typeof_str_to_re] at hNe
      | _ => simp [__eo_typeof_str_to_re] at hNe
  | _ => simp [__eo_typeof_str_to_re] at hNe

end ReInterCstringProof
