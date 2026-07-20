module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrSubstrContainsSupport

theorem eo_typeof_str_substr_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_substr A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Int ∧ C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_substr] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case UOp opb =>
          cases opb <;> simp at h ⊢
          case Int =>
            cases C <;> simp at h ⊢
            case UOp opc =>
              cases opc <;> simp at h ⊢

theorem eo_typeof_str_substr_result_of_seq_args
    (T : Term)
    (h : __eo_typeof_str_substr
      (Term.Apply Term.Seq T) Term.Int Term.Int ≠ Term.Stuck) :
    __eo_typeof_str_substr
        (Term.Apply Term.Seq T) Term.Int Term.Int =
      Term.Apply Term.Seq T := by
  cases T <;>
    simp [__eo_typeof_str_substr, __eo_requires, __eo_eq, native_ite,
      native_teq, SmtEval.native_not, __eo_and, native_and] at h ⊢

theorem eo_typeof_str_concat_args_of_ne_stuck
    (A B : Term)
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

theorem eo_typeof_str_concat_result_of_seq_args
    (T : Term)
    (h : __eo_typeof_str_concat
      (Term.Apply Term.Seq T) (Term.Apply Term.Seq T) ≠ Term.Stuck) :
    __eo_typeof_str_concat
        (Term.Apply Term.Seq T) (Term.Apply Term.Seq T) =
      Term.Apply Term.Seq T := by
  cases T <;>
    simp [__eo_typeof_str_concat, __eo_requires, __eo_eq, native_ite,
      native_teq, SmtEval.native_not, __eo_and, native_and] at h ⊢

theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

theorem smtx_eval_str_substr_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_substr x y z) =
      __smtx_model_eval_str_substr
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_str_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_plus_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_geq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem native_seq_extract_decomp
    (xs : List SmtValue) (i n : native_Int) :
    ∃ before after, xs = before ++ native_seq_extract xs i n ++ after := by
  unfold native_seq_extract
  dsimp only
  by_cases hi : i < 0
  · exact ⟨[], xs, by simp [hi]⟩
  · by_cases hn : n ≤ 0
    · exact ⟨[], xs, by simp [hi, hn]⟩
    · by_cases hlen : i ≥ Int.ofNat xs.length
      · have hd : decide (i ≥ Int.ofNat xs.length) = true :=
          decide_eq_true hlen
        refine ⟨[], xs, ?_⟩
        simp only [hi, hn, hd, decide_false, Bool.false_or,
          Bool.or_false, Bool.true_or, ↓reduceIte,
          List.append_nil, List.nil_append]
      · have hd : decide (i ≥ Int.ofNat xs.length) = false :=
          decide_eq_false hlen
        let start := Int.toNat i
        let count := Int.toNat (min n (Int.ofNat xs.length - i))
        refine ⟨xs.take start, (xs.drop start).drop count, ?_⟩
        simp only [hi, hn, hd, decide_false, Bool.false_or,
          Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        change xs =
          (xs.take start ++ (xs.drop start).take count) ++
            (xs.drop start).drop count
        rw [List.append_assoc,
          List.take_append_drop count (xs.drop start),
          List.take_append_drop start xs]

theorem native_seq_contains_extract
    (xs : List SmtValue) (i n : native_Int) :
    native_seq_contains xs (native_seq_extract xs i n) = true := by
  rcases native_seq_extract_decomp xs i n with ⟨before, after, hXs⟩
  apply (StrContainsReplCharSupport.native_seq_contains_iff_decomp
    xs (native_seq_extract xs i n)).2
  exact ⟨before, after, hXs⟩

theorem native_seq_contains_extract_target_false
    (xs target : List SmtValue) (i n : native_Int)
    (hAbsent : native_seq_contains xs target = false) :
    native_seq_contains (native_seq_extract xs i n) target = false := by
  cases h : native_seq_contains (native_seq_extract xs i n) target
  · rfl
  · have hContradiction :=
      StrContainsReplCharSupport.native_seq_contains_trans xs
        (native_seq_extract xs i n) target
        (native_seq_contains_extract xs i n) h
    rw [hContradiction] at hAbsent
    contradiction

theorem native_seq_extract_append_left
    (xs ys : List SmtValue) (i n : native_Int)
    (hBound : i + n ≤ (xs.length : native_Int)) :
    native_seq_extract (xs ++ ys) i n = native_seq_extract xs i n := by
  by_cases hi : i < 0
  · simp [native_seq_extract, hi]
  · by_cases hn : n ≤ 0
    · simp [native_seq_extract, hi, hn]
    · have hiNonneg : 0 ≤ i := Int.le_of_not_gt hi
      have hnPos : 0 < n := Int.lt_of_not_ge hn
      have hiLtXs : i < Int.ofNat xs.length := by
        have hStep : i < i + n := by
          simpa using Int.add_lt_add_left hnPos i
        exact Int.lt_of_lt_of_le hStep hBound
      have hLenLe :
          Int.ofNat xs.length ≤ Int.ofNat (xs ++ ys).length :=
        Int.ofNat_le.mpr (by simp)
      have hiLtAppend : i < Int.ofNat (xs ++ ys).length := by
        exact Int.lt_of_lt_of_le hiLtXs hLenLe
      have hnLeXs : n ≤ Int.ofNat xs.length - i := by
        exact Int.le_sub_left_of_add_le hBound
      have hnLeAppend : n ≤ Int.ofNat (xs ++ ys).length - i := by
        exact Int.le_trans hnLeXs (Int.sub_le_sub_right hLenLe i)
      have hMinXs : min n (Int.ofNat xs.length - i) = n :=
        Int.min_eq_left hnLeXs
      have hMinAppend :
          min n (Int.ofNat (xs ++ ys).length - i) = n :=
        Int.min_eq_left hnLeAppend
      have hiCast : (Int.toNat i : native_Int) = i :=
        Int.toNat_of_nonneg hiNonneg
      have hnCast : (Int.toNat n : native_Int) = n :=
        Int.toNat_of_nonneg (Int.le_of_lt hnPos)
      have hStartLe : Int.toNat i ≤ xs.length := by
        apply Int.ofNat_le.mp
        rw [hiCast]
        exact Int.le_of_lt hiLtXs
      have hBoundNat : Int.toNat i + Int.toNat n ≤ xs.length := by
        apply Int.ofNat_le.mp
        rw [← Int.ofNat_add_ofNat, hiCast, hnCast]
        exact hBound
      have hTakeLe :
          Int.toNat n ≤ (xs.drop (Int.toNat i)).length := by
        rw [List.length_drop]
        omega
      have hdXs : decide (i ≥ Int.ofNat xs.length) = false :=
        decide_eq_false (Int.not_le_of_gt hiLtXs)
      have hdAppend :
          decide (i ≥ Int.ofNat (xs ++ ys).length) = false :=
        decide_eq_false (Int.not_le_of_gt hiLtAppend)
      unfold native_seq_extract
      simp only [hi, hn, hdXs, hdAppend, decide_false,
        Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
        hMinXs, hMinAppend]
      rw [List.drop_append_of_le_length hStartLe,
        List.take_append_of_le_length hTakeLe]

end StrSubstrContainsSupport
