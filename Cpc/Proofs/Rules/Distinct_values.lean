import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem eo_ite_eq_false_guard_true {a b d : Term} :
    __eo_ite (__eo_eq a b) (Term.Boolean false) d = Term.Boolean true ->
    __eo_eq a b = Term.Boolean false ∧ d = Term.Boolean true := by
  intro h
  unfold __eo_ite at h
  by_cases ht : native_teq (__eo_eq a b) (Term.Boolean true) = true
  · simp [ht, native_ite] at h
  · by_cases hf : native_teq (__eo_eq a b) (Term.Boolean false) = true
    · have hEq : __eo_eq a b = Term.Boolean false := by
        simpa [native_teq] using hf
      simp [ht, hf, native_ite] at h
      exact ⟨hEq, h⟩
    · simp [ht, hf, native_ite] at h

private theorem eo_ite_eq_true_cases (c t e : Term) :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

private theorem eo_eq_false_ne {a b : Term} :
    __eo_eq a b = Term.Boolean false -> a ≠ b := by
  intro h hEq
  subst b
  cases a <;> simp [__eo_eq, native_teq] at h

private theorem eo_eq_true_eq {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  cases a <;> cases b <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals simpa [eq_comm, and_assoc] using h

private theorem eo_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;> simp [__eo_and, __eo_requires, native_teq,
    native_ite, SmtEval.native_and, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> simp at h

private theorem eo_or_true {a b : Term} :
    __eo_or a b = Term.Boolean true ->
    a = Term.Boolean true ∨ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_or, native_or, __eo_requires, native_teq, native_ite,
      SmtEval.native_not] at h ⊢
  case Boolean.Boolean x y =>
    cases x <;> cases y <;> simp [native_or] at h ⊢
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂
    · subst w₂
      simp [native_teq] at h
    · simp [native_teq, hw] at h

private theorem map_native_ssm_char_char :
    ∀ s : native_String,
      List.map (native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | _ :: cs => by
      simp [Function.comp_def, native_ssm_char_of_value,
        map_native_ssm_char_char cs]

private theorem are_distinct_int_true {a b : Term} :
    __are_distinct_terms_type a b (Term.UOp UserOp.Int) = Term.Boolean true ->
    ∃ m n, a = Term.Numeral m ∧ b = Term.Numeral n := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_z,
      __eo_is_z_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i m n
    exact ⟨m, n, rfl, rfl⟩

private theorem are_distinct_real_true {a b : Term} :
    __are_distinct_terms_type a b (Term.UOp UserOp.Real) = Term.Boolean true ->
    ∃ q r, a = Term.Rational q ∧ b = Term.Rational r := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_q,
      __eo_is_q_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i q r
    exact ⟨q, r, rfl, rfl⟩

private theorem are_distinct_string_true {a b : Term} :
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
      Term.Boolean true ->
    ∃ s t, a = Term.String s ∧ b = Term.String t := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_str,
      __eo_is_str_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i s t
    exact ⟨s, t, rfl, rfl⟩

private theorem are_distinct_bin_true {a b n : Term} :
    __are_distinct_terms_type a b (Term.Apply (Term.UOp UserOp.BitVec) n) =
      Term.Boolean true ->
    ∃ w k w' k', a = Term.Binary w k ∧ b = Term.Binary w' k' := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_bin,
      __eo_is_bin_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i w k w' k'
    exact ⟨w, k, w', k', rfl, rfl⟩

private theorem are_distinct_bool_true {a b : Term} :
    __are_distinct_terms_type a b Term.Bool = Term.Boolean true ->
    ∃ x y, a = Term.Boolean x ∧ b = Term.Boolean y := by
  intro h
  cases a <;> cases b <;>
    simp [__are_distinct_terms_type.eq_def, __eo_and, __eo_is_bool,
      __eo_is_bool_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at h
  · rename_i x y
    exact ⟨x, y, rfl, rfl⟩

private theorem model_eval_eq_false_of_literal_ne
    (M : SmtModel) {a b : Term}
    (ha : a ≠ b)
    (hLit :
      (∃ m n, a = Term.Numeral m ∧ b = Term.Numeral n) ∨
      (∃ q r, a = Term.Rational q ∧ b = Term.Rational r) ∨
      (∃ s t, a = Term.String s ∧ b = Term.String t) ∨
      (∃ w n w' n', a = Term.Binary w n ∧ b = Term.Binary w' n') ∨
      (∃ x y, a = Term.Boolean x ∧ b = Term.Boolean y)) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  rcases hLit with ⟨m, n, rfl, rfl⟩
    | ⟨q, r, rfl, rfl⟩
    | ⟨s, t, rfl, rfl⟩
    | ⟨w, n, w', n', rfl, rfl⟩
    | ⟨x, y, rfl, rfl⟩
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Numeral m))
        (__smtx_model_eval M (SmtTerm.Numeral n)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Rational q))
        (__smtx_model_eval M (SmtTerm.Rational r)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_3, __smtx_model_eval.eq_3]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.String s))
        (__smtx_model_eval M (SmtTerm.String t)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_4, __smtx_model_eval.eq_4]
    simp [__smtx_model_eval_eq, native_veq]
    intro hPack
    apply ha
    have hUnpack := congrArg native_unpack_string hPack
    simpa [native_unpack_string, native_pack_string, Smtm.native_unpack_pack_seq,
      map_native_ssm_char_char] using hUnpack
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Binary w n))
        (__smtx_model_eval M (SmtTerm.Binary w' n')) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_5, __smtx_model_eval.eq_5]
    simpa [__smtx_model_eval_eq, native_veq] using ha
  · change __smtx_model_eval_eq (__smtx_model_eval M (SmtTerm.Boolean x))
        (__smtx_model_eval M (SmtTerm.Boolean y)) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_1, __smtx_model_eval.eq_1]
    simpa [__smtx_model_eval_eq, native_veq] using ha

private theorem are_distinct_terms_type_primitive_model_eval_eq_false
    (M : SmtModel) (a b T : Term) :
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b T = Term.Boolean true ->
    (T = Term.UOp UserOp.Int ∨
      T = Term.UOp UserOp.Real ∨
      T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∨
      (∃ n, T = Term.Apply (Term.UOp UserOp.BitVec) n) ∨
      T = Term.Bool) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro hEq hDistinct hT
  have hNe : a ≠ b := eo_eq_false_ne hEq
  rcases hT with rfl | rfl | rfl | ⟨n, rfl⟩ | rfl
  · rcases are_distinct_int_true hDistinct with ⟨m, n, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe (Or.inl ⟨m, n, rfl, rfl⟩)
  · rcases are_distinct_real_true hDistinct with ⟨q, r, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe (Or.inr <| Or.inl ⟨q, r, rfl, rfl⟩)
  · rcases are_distinct_string_true hDistinct with ⟨s, t, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inl ⟨s, t, rfl, rfl⟩)
  · rcases are_distinct_bin_true hDistinct with ⟨w, k, w', k', rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨w, k, w', k', rfl, rfl⟩)
  · rcases are_distinct_bool_true hDistinct with ⟨x, y, rfl, rfl⟩
    exact model_eval_eq_false_of_literal_ne M hNe
      (Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨x, y, rfl, rfl⟩)

private theorem smtx_model_eval_eq_false_of_ne_not_reglan
    {v₁ v₂ : SmtValue}
    (hNe : v₁ ≠ v₂)
    (hReg :
      ¬ ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂) :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  cases v₁ <;> cases v₂ <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals exact hNe

private theorem set_singleton_value_model_eval_eq_false_of_elem
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false ->
    __smtx_model_eval_eq (__smtx_model_eval_set_singleton v₁)
        (__smtx_model_eval_set_singleton v₂) =
      SmtValue.Boolean false := by
  intro hElemEqFalse
  have hElemNe : v₁ ≠ v₂ := by
    intro hSame
    subst v₂
    have hRefl : __smtx_model_eval_eq v₁ v₁ = SmtValue.Boolean true :=
      RuleProofs.smtx_model_eval_eq_refl v₁
    rw [hRefl] at hElemEqFalse
    cases hElemEqFalse
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    simp [__smtx_model_eval_set_singleton] at hEq
    exact hElemNe hEq.1
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    simp [__smtx_model_eval_set_singleton] at hReg₁

private theorem set_singleton_value_set_empty_value_model_eval_eq_false
    (v : SmtValue) (T : SmtType) :
    __smtx_model_eval_eq (__smtx_model_eval_set_singleton v)
        (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))) =
      SmtValue.Boolean false := by
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    simp [__smtx_model_eval_set_singleton] at hEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    simp [__smtx_model_eval_set_singleton] at hReg₁

private theorem set_empty_value_set_singleton_value_model_eval_eq_false
    (T : SmtType) (v : SmtValue) :
    __smtx_model_eval_eq (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)))
        (__smtx_model_eval_set_singleton v) =
      SmtValue.Boolean false := by
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    simp [__smtx_model_eval_set_singleton] at hEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    cases hReg₁

private theorem set_singleton_set_singleton_model_eval_eq_false_of_head
    (M : SmtModel) (e₁ e₂ : Term) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadEqFalse
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₁)))
      (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e₂))) =
    SmtValue.Boolean false
  rw [__smtx_model_eval.eq_122, __smtx_model_eval.eq_122]
  exact set_singleton_value_model_eval_eq_false_of_elem hHeadEqFalse

private theorem set_singleton_set_empty_model_eval_eq_false
    (M : SmtModel) (e U : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.UOp1 UserOp1.set_empty
              (Term.Apply (Term.UOp UserOp.Set) U)))) =
      SmtValue.Boolean false := by
  intro hEmptyTrans
  have hSetTy :
      ∃ T, __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U) =
        SmtType.Set T := by
    cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U)
    case Set T =>
      exact ⟨T, rfl⟩
    all_goals
      exfalso
      apply hEmptyTrans
      change __smtx_typeof
          (__eo_to_smt_set_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U))) =
        SmtType.None
      rw [hTy]
      simp [__eo_to_smt_set_empty]
  rcases hSetTy with ⟨T, hTy⟩
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e)))
      (__smtx_model_eval M
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U)))) =
    SmtValue.Boolean false
  rw [hTy, __smtx_model_eval.eq_122]
  change __smtx_model_eval_eq
      (__smtx_model_eval_set_singleton (__smtx_model_eval M (__eo_to_smt e)))
      (__smtx_model_eval M (SmtTerm.set_empty T)) =
    SmtValue.Boolean false
  rw [__smtx_model_eval.eq_121]
  exact set_singleton_value_set_empty_value_model_eval_eq_false
    (__smtx_model_eval M (__eo_to_smt e)) T

private theorem set_empty_set_singleton_model_eval_eq_false
    (M : SmtModel) (U e : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.UOp1 UserOp1.set_empty
              (Term.Apply (Term.UOp UserOp.Set) U))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e))) =
      SmtValue.Boolean false := by
  intro hEmptyTrans
  have hSetTy :
      ∃ T, __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U) =
        SmtType.Set T := by
    cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U)
    case Set T =>
      exact ⟨T, rfl⟩
    all_goals
      exfalso
      apply hEmptyTrans
      change __smtx_typeof
          (__eo_to_smt_set_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U))) =
        SmtType.None
      rw [hTy]
      simp [__eo_to_smt_set_empty]
  rcases hSetTy with ⟨T, hTy⟩
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt_set_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U))))
      (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt e))) =
    SmtValue.Boolean false
  rw [hTy, __smtx_model_eval.eq_122]
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.set_empty T))
      (__smtx_model_eval_set_singleton (__smtx_model_eval M (__eo_to_smt e))) =
    SmtValue.Boolean false
  rw [__smtx_model_eval.eq_121]
  exact set_empty_value_set_singleton_value_model_eval_eq_false T
    (__smtx_model_eval M (__eo_to_smt e))

private theorem seq_is_non_empty_shape {t : Term} :
    __seq_is_non_empty t = Term.Boolean true ->
    (∃ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e) ∨
      (∃ e ts,
        t =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.UOp UserOp.seq_unit) e))
            ts) := by
  intro h
  cases t <;> simp [__seq_is_non_empty] at h
  case Apply f x =>
    cases f <;> try simp [__seq_is_non_empty] at h
    case UOp op =>
      cases op <;> simp [__seq_is_non_empty] at h
      exact Or.inl ⟨x, rfl⟩
    case Apply g y =>
      cases g <;> try simp [__seq_is_non_empty] at h
      case UOp op =>
        cases op <;> try simp [__seq_is_non_empty] at h
        case str_concat =>
          cases y <;> try simp [__seq_is_non_empty] at h
          case Apply u e =>
            cases u <;> try simp [__seq_is_non_empty] at h
            case UOp op =>
              cases op <;> simp [__seq_is_non_empty] at h
              exact Or.inr ⟨e, x, rfl⟩

private theorem native_pack_seq_ne_empty_of_length_pos
    (T : SmtType) {xs : List SmtValue} (hPos : 0 < xs.length) :
    native_pack_seq T xs ≠ SmtSeq.empty T := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenZero : xs.length = 0 := by
    have hLen := congrArg List.length hUnpack
    simpa [Smtm.native_unpack_pack_seq, native_unpack_seq] using hLen
  omega

private theorem native_pack_seq_ne_empty_of_length_pos_any
    (T U : SmtType) {xs : List SmtValue} (hPos : 0 < xs.length) :
    native_pack_seq T xs ≠ SmtSeq.empty U := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenZero : xs.length = 0 := by
    have hLen := congrArg List.length hUnpack
    simpa [Smtm.native_unpack_pack_seq, native_unpack_seq] using hLen
  omega

private theorem seq_is_non_empty_model_eval
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __seq_is_non_empty t = Term.Boolean true ->
    ∃ T xs,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Seq (native_pack_seq T xs) ∧
      0 < xs.length := by
  intro hTrans hNonEmpty
  rcases seq_is_non_empty_shape hNonEmpty with
    ⟨e, rfl⟩ | ⟨e, ts, rfl⟩
  · let v := __smtx_model_eval M (__eo_to_smt e)
    refine ⟨__smtx_typeof_value v, [v], ?_, by simp⟩
    change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v])
    simp [__smtx_model_eval, v, native_pack_seq]
  · let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
    let v := __smtx_model_eval M (__eo_to_smt e)
    have hUnitEval :
        __smtx_model_eval M (__eo_to_smt unit) =
          SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v]) := by
      change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
        SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v])
      simp [__smtx_model_eval, unit, v, native_pack_seq]
    have hConcatNN :
        __smtx_typeof (__eo_to_smt (mkConcat unit ts)) ≠ SmtType.None := by
      simpa [unit, mkConcat] using hTrans
    rcases str_concat_args_of_non_none unit ts hConcatNN with
      ⟨T, _hUnitTy, hTsTy⟩
    have hTailTy :=
      smt_model_eval_preserves_type M hM (__eo_to_smt ts) (SmtType.Seq T)
        hTsTy (seq_ne_none T) (type_inhabited_seq T)
    rcases seq_value_canonical hTailTy with ⟨tail, hTailEval⟩
    refine
      ⟨__smtx_typeof_value v, v :: native_unpack_seq tail, ?_, by simp⟩
    rw [smtx_model_eval_str_concat_term_eq, hUnitEval, hTailEval]
    change
      __smtx_model_eval_str_concat
        (SmtValue.Seq (native_pack_seq (__smtx_typeof_value v) [v]))
        (SmtValue.Seq tail) =
      SmtValue.Seq
        (native_pack_seq (__smtx_typeof_value v) (v :: native_unpack_seq tail))
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem smt_eval_eq_false_implies_ne
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false ->
    v₁ ≠ v₂ := by
  intro hEq hSame
  subst v₂
  have hRefl : __smtx_model_eval_eq v₁ v₁ = SmtValue.Boolean true :=
    RuleProofs.smtx_model_eval_eq_refl v₁
  rw [hRefl] at hEq
  cases hEq

private theorem smtx_model_eval_eq_false_symm
    {v₁ v₂ : SmtValue} :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false ->
    __smtx_model_eval_eq v₂ v₁ = SmtValue.Boolean false := by
  intro hEq
  by_cases hReg :
      ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂
  · rcases hReg with ⟨r₁, r₂, rfl, rfl⟩
    change SmtValue.Boolean (native_re_ext_eq r₂ r₁) = SmtValue.Boolean false
    change SmtValue.Boolean (native_re_ext_eq r₁ r₂) = SmtValue.Boolean false at hEq
    simp at hEq ⊢
    rcases hEq with ⟨s, hs, hNe⟩
    exact ⟨s, hs, fun hEq => hNe hEq.symm⟩
  · cases v₁ <;> cases v₂ <;>
      simp [__smtx_model_eval_eq] at hEq hReg ⊢
    all_goals
      exact native_veq_false_symm hEq

private theorem eval_seq_unit_pack (M : SmtModel) (e : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtValue.Seq
        (native_pack_seq
          (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
          [__smtx_model_eval M (__eo_to_smt e)]) := by
  change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
    SmtValue.Seq
      (native_pack_seq
        (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
        [__smtx_model_eval M (__eo_to_smt e)])
  simp [__smtx_model_eval, native_pack_seq]

private theorem eval_concat_seq_unit_pack
    (M : SmtModel) (hM : model_total_typed M) (e tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ->
    ∃ ss,
      __smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtValue.Seq
          (native_pack_seq
            (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
            (__smtx_model_eval M (__eo_to_smt e) :: native_unpack_seq ss)) := by
  intro hTrans
  let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat unit tail)) ≠ SmtType.None := by
    simpa [unit] using hTrans
  rcases str_concat_args_of_non_none unit tail hConcatNN with
    ⟨T, _hUnitTy, hTailTy⟩
  have hTailValTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt tail) (SmtType.Seq T)
      hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨ss, hTailEval⟩
  refine ⟨ss, ?_⟩
  rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
    native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem eval_concat_seq_unit_pack_with_tail
    (M : SmtModel) (hM : model_total_typed M) (e tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ->
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.Seq ss ∧
        __smtx_elem_typeof_seq_value ss =
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) ∧
        __smtx_model_eval M
            (__eo_to_smt
              (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
          SmtValue.Seq
            (native_pack_seq
              (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)))
              (__smtx_model_eval M (__eo_to_smt e) ::
                native_unpack_seq ss)) := by
  intro hTrans
  let unit := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat unit tail)) ≠ SmtType.None := by
    simpa [unit] using hTrans
  rcases str_concat_args_of_non_none unit tail hConcatNN with
    ⟨T, hUnitTy, hTailTy⟩
  have hArgTyInfo :=
    seq_unit_type_eq_arg_of_eq
      (t := __eo_to_smt e) (A := T) (by
        simpa [unit] using hUnitTy)
  have hArgNonNone :
      term_has_non_none_type (__eo_to_smt e) := by
    unfold term_has_non_none_type
    rw [hArgTyInfo.1]
    exact hArgTyInfo.2
  have hHeadValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) = T :=
    (smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt e)
      hArgNonNone).trans hArgTyInfo.1
  have hTailValTy :=
    smt_model_eval_preserves_type M hM (__eo_to_smt tail) (SmtType.Seq T)
      hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨ss, hTailEval⟩
  have hTailElemTy :
      __smtx_elem_typeof_seq_value ss = T := by
    have hValTy := hTailValTy
    rw [hTailEval] at hValTy
    exact elem_typeof_seq_value_of_typeof_seq_value
      (by simpa [__smtx_typeof_value] using hValTy)
  refine ⟨ss, hTailEval, hTailElemTy.trans hHeadValTy.symm, ?_⟩
  rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
    native_unpack_seq, __smtx_elem_typeof_seq_value]

private theorem eval_seq_empty_seq
    (M : SmtModel) (U : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))) =
      SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) := by
  intro hTrans
  by_cases hU : __eo_to_smt_type U = SmtType.None
  · exfalso
    apply hTrans
    change
      __smtx_typeof
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtType.None
    rw [TranslationProofs.eo_to_smt_type_seq]
    simp [__smtx_typeof_guard, hU, native_ite, native_Teq,
      __eo_to_smt_seq_empty]
  · change
      __smtx_model_eval M
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U))
    rw [TranslationProofs.eo_to_smt_type_seq]
    simp [__smtx_typeof_guard, hU, native_ite, native_Teq,
      __eo_to_smt_seq_empty, __smtx_model_eval]

private theorem seq_is_non_empty_ne_seq_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (t U : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __seq_is_non_empty t = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))) =
      SmtValue.Boolean false := by
  intro htTrans hEmptyTrans hNonEmpty
  rcases seq_is_non_empty_model_eval M hM t htTrans hNonEmpty with
    ⟨T, xs, hEvalT, hPos⟩
  have hEvalEmpty := eval_seq_empty_seq M U hEmptyTrans
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalT, hEvalEmpty] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_empty_of_length_pos_any T
      (__eo_to_smt_type U) hPos hSeqEq
  · rintro ⟨r₁, r₂, hR1, _hR2⟩
    rw [hEvalT] at hR1
    cases hR1

private theorem seq_empty_ne_seq_is_non_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (U t : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    RuleProofs.eo_has_smt_translation t ->
    __seq_is_non_empty t = Term.Boolean true ->
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
      (__smtx_model_eval M (__eo_to_smt t)) =
      SmtValue.Boolean false := by
  intro hEmptyTrans htTrans hNonEmpty
  rcases seq_is_non_empty_model_eval M hM t htTrans hNonEmpty with
    ⟨T, xs, hEvalT, hPos⟩
  have hEvalEmpty := eval_seq_empty_seq M U hEmptyTrans
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalT, hEvalEmpty] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_empty_of_length_pos_any T
      (__eo_to_smt_type U) hPos hSeqEq.symm
  · rintro ⟨r₁, r₂, hR1, _hR2⟩
    rw [hEvalEmpty] at hR1
    cases hR1

private theorem seq_distinct_terms_right_empty_non_empty
    {t U T : Term} :
    __seq_distinct_terms t
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true ->
    __seq_is_non_empty t = Term.Boolean true := by
  intro hDistinct
  change __seq_distinct_terms t
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true at hDistinct
  cases T <;> cases t <;> simp [__seq_distinct_terms] at hDistinct ⊢
  all_goals exact hDistinct

private theorem seq_distinct_terms_left_empty_non_empty
    {U t T : Term} :
    __seq_distinct_terms
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true ->
    __seq_is_non_empty t = Term.Boolean true := by
  intro hDistinct
  change __seq_distinct_terms
      (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true at hDistinct
  cases t <;> try
    (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
     all_goals exact hDistinct)
  case UOp1 op arg =>
    cases op
    case seq_empty =>
      cases arg <;> try
        (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
         all_goals exact hDistinct)
      case Apply f x =>
        cases f <;> try
          (cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
           all_goals exact hDistinct)
        case UOp fop =>
          cases fop <;>
            cases T <;>
              simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
          all_goals exact hDistinct
    all_goals
      cases T <;> simp [__seq_distinct_terms, __seq_is_non_empty] at hDistinct ⊢
      all_goals exact hDistinct

private theorem seq_distinct_terms_right_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (t U T : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    __seq_distinct_terms t
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) T =
      Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)))) =
      SmtValue.Boolean false := by
  intro htTrans hEmptyTrans hDistinct
  exact seq_is_non_empty_ne_seq_empty_model_eval_eq_false
    M hM t U htTrans hEmptyTrans
    (seq_distinct_terms_right_empty_non_empty hDistinct)

private theorem seq_distinct_terms_left_empty_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (U t T : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) ->
    RuleProofs.eo_has_smt_translation t ->
    __seq_distinct_terms
      (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) t T =
      Term.Boolean true ->
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U))))
      (__smtx_model_eval M (__eo_to_smt t)) =
      SmtValue.Boolean false := by
  intro hEmptyTrans htTrans hDistinct
  exact seq_empty_ne_seq_is_non_empty_model_eval_eq_false
    M hM U t hEmptyTrans htTrans
    (seq_distinct_terms_left_empty_non_empty hDistinct)

private theorem are_distinct_terms_type_seq_true_seq_distinct
    {a b U : Term} :
    U ≠ Term.UOp UserOp.Char ->
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Seq) U) =
      Term.Boolean true ->
    __seq_distinct_terms a b U = Term.Boolean true := by
  intro hU hDistinct
  cases U
  case UOp op =>
    cases op
    case Char =>
      exact False.elim (hU rfl)
    all_goals
      cases a <;> cases b <;>
        simp [__are_distinct_terms_type.eq_def] at hDistinct ⊢
      all_goals exact hDistinct
  all_goals
    cases a <;> cases b <;>
      simp [__are_distinct_terms_type.eq_def] at hDistinct ⊢
    all_goals exact hDistinct

private theorem eo_eq_false_left_ne_stuck {a b : Term} :
    __eo_eq a b = Term.Boolean false -> a ≠ Term.Stuck := by
  intro hEq hStuck
  subst a
  simp [__eo_eq] at hEq

private theorem eo_eq_false_right_ne_stuck {a b : Term} :
    __eo_eq a b = Term.Boolean false -> b ≠ Term.Stuck := by
  intro hEq hStuck
  subst b
  cases a <;> simp [__eo_eq] at hEq

private theorem seq_distinct_terms_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_eq a b = Term.Boolean false ->
    __seq_distinct_terms a b U = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans _hEqFalse hDistinct
  by_cases hbEmpty :
      ∃ V, b = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
  · rcases hbEmpty with ⟨V, rfl⟩
    exact seq_distinct_terms_right_empty_model_eval_eq_false
      M hM a V U haTrans hbTrans hDistinct
  · by_cases haEmpty :
        ∃ V, a = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
    · rcases haEmpty with ⟨V, rfl⟩
      exact seq_distinct_terms_left_empty_model_eval_eq_false
        M hM V b U haTrans hbTrans hDistinct
    · -- The remaining cases are the recursive non-empty sequence spines.
      sorry

private theorem are_distinct_terms_type_set_true_not_subset
    {a b U : Term} :
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Set) U) =
      Term.Boolean true ->
    __set_is_not_subset a b U = Term.Boolean true ∨
      __set_is_not_subset b a U = Term.Boolean true := by
  intro hDistinct
  have hOr :
      __eo_or (__set_is_not_subset a b U)
          (__set_is_not_subset b a U) =
        Term.Boolean true := by
    cases a <;> cases b <;>
      simp [__are_distinct_terms_type.eq_def] at hDistinct ⊢
    all_goals exact hDistinct
  exact eo_or_true hOr

private theorem set_is_not_subset_singleton_singleton_model_eval_eq_false
    (M : SmtModel) (e₁ e₂ U : Term) :
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __set_is_not_subset (Term.Apply (Term.UOp UserOp.set_singleton) e₁)
        (Term.Apply (Term.UOp UserOp.set_singleton) e₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadSound hNotSubset
  have hBranch :
      __eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
          (__are_distinct_terms_type e₁ e₂ U) =
        Term.Boolean true := by
    change __set_is_not_subset
        (Term.Apply (Term.UOp UserOp.set_singleton) e₁)
        (Term.Apply (Term.UOp UserOp.set_singleton) e₂) U =
      Term.Boolean true at hNotSubset
    cases U <;>
      (rw [__set_is_not_subset.eq_def] at hNotSubset
       simp only at hNotSubset)
    all_goals first | exact hNotSubset | cases hNotSubset
  rcases eo_ite_eq_false_guard_true hBranch with
    ⟨hHeadEqFalse, hHeadDistinct⟩
  exact set_singleton_set_singleton_model_eval_eq_false_of_head M e₁ e₂
    (hHeadSound hHeadEqFalse hHeadDistinct)

private theorem set_is_not_subset_singleton_singleton_model_eval_eq_false_symm
    (M : SmtModel) (e₁ e₂ U : Term) :
    (__eo_eq e₂ e₁ = Term.Boolean false ->
      __are_distinct_terms_type e₂ e₁ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₂))
          (__smtx_model_eval M (__eo_to_smt e₁)) =
        SmtValue.Boolean false) ->
    __set_is_not_subset (Term.Apply (Term.UOp UserOp.set_singleton) e₂)
        (Term.Apply (Term.UOp UserOp.set_singleton) e₁) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadSound hNotSubset
  exact smtx_model_eval_eq_false_symm
    (set_is_not_subset_singleton_singleton_model_eval_eq_false
      M e₂ e₁ U hHeadSound hNotSubset)

private theorem set_is_not_subset_singleton_empty_model_eval_eq_false
    (M : SmtModel) (e U T : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) ->
    __set_is_not_subset (Term.Apply (Term.UOp UserOp.set_singleton) e)
        (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) T =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.UOp1 UserOp1.set_empty
              (Term.Apply (Term.UOp UserOp.Set) U)))) =
      SmtValue.Boolean false := by
  intro hEmptyTrans _hNotSubset
  exact set_singleton_set_empty_model_eval_eq_false M e U hEmptyTrans

private theorem set_is_not_subset_singleton_empty_model_eval_eq_false_symm
    (M : SmtModel) (e U T : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) ->
    __set_is_not_subset (Term.Apply (Term.UOp UserOp.set_singleton) e)
        (Term.UOp1 UserOp1.set_empty (Term.Apply (Term.UOp UserOp.Set) U)) T =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.UOp1 UserOp1.set_empty
              (Term.Apply (Term.UOp UserOp.Set) U))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) e))) =
      SmtValue.Boolean false := by
  intro hEmptyTrans _hNotSubset
  exact set_empty_set_singleton_model_eval_eq_false M U e hEmptyTrans

private theorem native_pack_seq_ne_of_length_ne
    (T U : SmtType) {xs ys : List SmtValue}
    (hLen : xs.length ≠ ys.length) :
    native_pack_seq T xs ≠ native_pack_seq U ys := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenEq := congrArg List.length hUnpack
  apply hLen
  simpa [Smtm.native_unpack_pack_seq] using hLenEq

private theorem native_pack_seq_cons_ne_of_head_ne
    (T U : SmtType) {x y : SmtValue} {xs ys : List SmtValue}
    (hHead : x ≠ y) :
    native_pack_seq T (x :: xs) ≠ native_pack_seq U (y :: ys) := by
  intro hEq
  change SmtSeq.cons x (native_pack_seq T xs) =
    SmtSeq.cons y (native_pack_seq U ys) at hEq
  injection hEq with hxy _
  exact hHead hxy

private theorem seq_unit_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (e₁ e₂ : Term) :
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  have hEval₁ := eval_seq_unit_pack M e₁
  have hEval₂ := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := []) (ys := []) hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail₁ e₂ tail₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  rcases eval_concat_seq_unit_pack M hM e₁ tail₁ hLeftTrans with
    ⟨ss₁, hEval₁⟩
  rcases eval_concat_seq_unit_pack M hM e₂ tail₂ hRightTrans with
    ⟨ss₂, hEval₂⟩
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂)
      (xs := native_unpack_seq ss₁) (ys := native_unpack_seq ss₂)
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail e₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  rcases eval_concat_seq_unit_pack M hM e₁ tail hLeftTrans with
    ⟨ss, hEvalLeft⟩
  have hEvalRight := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := native_unpack_seq ss) (ys := [])
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_concat_seq_unit_model_eval_eq_false_of_head
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ e₂ tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
        (__smtx_model_eval M (__eo_to_smt e₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hHeadEqFalse
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hHeadNe : v₁ ≠ v₂ := by
    simpa [v₁, v₂] using smt_eval_eq_false_implies_ne hHeadEqFalse
  have hEvalLeft := eval_seq_unit_pack M e₁
  rcases eval_concat_seq_unit_pack M hM e₂ tail hRightTrans with
    ⟨ss, hEvalRight⟩
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_cons_ne_of_head_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (x := v₁) (y := v₂) (xs := []) (ys := native_unpack_seq ss)
      hHeadNe hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_arg_translation_of_translation (e : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e) ->
    RuleProofs.eo_has_smt_translation e := by
  intro hTrans hArgNone
  apply hTrans
  change __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt e)) = SmtType.None
  simp [__smtx_typeof, __smtx_typeof_guard_wf, __smtx_type_wf,
    __smtx_type_wf_component, __smtx_type_wf_rec, native_inhabited_type,
    __smtx_type_default, __smtx_value_canonical_bool, native_and, native_ite,
    hArgNone]

private theorem str_concat_arg_translations_of_translation (x y : Term) :
    RuleProofs.eo_has_smt_translation (mkConcat x y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases str_concat_args_of_non_none x y hTrans with ⟨T, hxTy, hyTy⟩
  constructor
  · intro hNone
    rw [hxTy] at hNone
    exact seq_ne_none T hNone
  · intro hNone
    rw [hyTy] at hNone
    exact seq_ne_none T hNone

private theorem concat_seq_unit_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail e₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    __seq_is_non_empty tail = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hTailNonEmpty
  have hTailTrans :
      RuleProofs.eo_has_smt_translation tail :=
    (str_concat_arg_translations_of_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail hLeftTrans).2
  rcases seq_is_non_empty_model_eval M hM tail hTailTrans hTailNonEmpty with
    ⟨T, xs, hTailEval, hPos⟩
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hEvalLeft :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_typeof_value v₁) (v₁ :: xs)) := by
    rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, Smtm.native_unpack_pack_seq,
      __smtx_elem_typeof_seq_value, v₁]
  have hEvalRight := eval_seq_unit_pack M e₂
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_of_length_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (xs := v₁ :: xs) (ys := [v₂]) (by
        intro hLen
        have hLeftGt : 1 < (v₁ :: xs).length := by
          simpa using Nat.succ_lt_succ hPos
        have hBad : 1 < [v₂].length := by
          rwa [← hLen]
        simp at hBad) hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ e₂ tail : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    __seq_is_non_empty tail = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hTailNonEmpty
  have hTailTrans :
      RuleProofs.eo_has_smt_translation tail :=
    (str_concat_arg_translations_of_translation
      (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail hRightTrans).2
  rcases seq_is_non_empty_model_eval M hM tail hTailTrans hTailNonEmpty with
    ⟨T, xs, hTailEval, hPos⟩
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  have hEvalLeft := eval_seq_unit_pack M e₁
  have hEvalRight :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_typeof_value v₂) (v₂ :: xs)) := by
    rw [smtx_model_eval_str_concat_term_eq, eval_seq_unit_pack, hTailEval]
    simp [__smtx_model_eval_str_concat, native_seq_concat, native_pack_seq,
      native_unpack_seq, Smtm.native_unpack_pack_seq,
      __smtx_elem_typeof_seq_value, v₂]
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEvalLeft, hEvalRight] at hEq
    injection hEq with hSeqEq
    exact native_pack_seq_ne_of_length_ne
      (__smtx_typeof_value v₁) (__smtx_typeof_value v₂)
      (xs := [v₁]) (ys := v₂ :: xs) (by
        intro hLen
        have hRightGt : 1 < (v₂ :: xs).length := by
          simpa using Nat.succ_lt_succ hPos
        have hBad : 1 < [v₁].length := by
          rwa [hLen]
        simp at hBad) hSeqEq
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEvalLeft] at hReg₁
    cases hReg₁

private theorem concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail₁ e₂ tail₂ : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt tail₁))
        (__smtx_model_eval M (__eo_to_smt tail₂)) =
      SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hTailEqFalse
  rcases eval_concat_seq_unit_pack_with_tail M hM e₁ tail₁ hLeftTrans with
    ⟨ss₁, hTailEval₁, hElem₁, hEval₁⟩
  rcases eval_concat_seq_unit_pack_with_tail M hM e₂ tail₂ hRightTrans with
    ⟨ss₂, hTailEval₂, hElem₂, hEval₂⟩
  have hTailNe : SmtValue.Seq ss₁ ≠ SmtValue.Seq ss₂ := by
    have hNe :=
      smt_eval_eq_false_implies_ne hTailEqFalse
    intro hEq
    apply hNe
    rw [hTailEval₁, hTailEval₂]
    exact hEq
  let v₁ := __smtx_model_eval M (__eo_to_smt e₁)
  let v₂ := __smtx_model_eval M (__eo_to_smt e₂)
  apply smtx_model_eval_eq_false_of_ne_not_reglan
  · intro hEq
    rw [hEval₁, hEval₂] at hEq
    injection hEq with hSeqEq
    change SmtSeq.cons v₁
        (native_pack_seq (__smtx_typeof_value v₁) (native_unpack_seq ss₁)) =
      SmtSeq.cons v₂
        (native_pack_seq (__smtx_typeof_value v₂) (native_unpack_seq ss₂)) at hSeqEq
    injection hSeqEq with _hHead hTailPackEq
    apply hTailNe
    have hTailEq : ss₁ = ss₂ := by
      calc
        ss₁ =
            native_pack_seq (__smtx_typeof_value v₁)
              (native_unpack_seq ss₁) := by
              rw [← hElem₁]
              exact (native_pack_unpack_seq ss₁).symm
        _ =
            native_pack_seq (__smtx_typeof_value v₂)
              (native_unpack_seq ss₂) := hTailPackEq
        _ = ss₂ := by
              rw [← hElem₂]
              exact native_pack_unpack_seq ss₂
    rw [hTailEq]
  · rintro ⟨r₁, r₂, hReg₁, _hReg₂⟩
    rw [hEval₁] at hReg₁
    cases hReg₁

private theorem seq_distinct_seq_unit_seq_unit_model_eval_eq_false
    (M : SmtModel) (e₁ e₂ U : Term) :
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hHeadSound hDistinct
  have hBranch :
      __eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
          (__are_distinct_terms_type e₁ e₂ U) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_false_guard_true hBranch with
    ⟨hHeadEqFalse, hHeadDistinct⟩
  exact seq_unit_seq_unit_model_eval_eq_false_of_head M e₁ e₂
    (hHeadSound hHeadEqFalse hHeadDistinct)

private theorem seq_distinct_concat_unit_concat_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail₁ e₂ tail₂ U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) ->
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    (__seq_distinct_terms tail₁ tail₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt tail₁))
          (__smtx_model_eval M (__eo_to_smt tail₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hHeadSound hTailSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_distinct_terms tail₁ tail₂ U) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁)) tail₁)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂)) tail₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_distinct_terms tail₁ tail₂ U) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailDistinct⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_head
      M hM e₁ tail₁ e₂ tail₂ hLeftTrans hRightTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact concat_seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ tail₁ e₂ tail₂ hLeftTrans hRightTrans
      (hTailSound hTailDistinct)

private theorem seq_distinct_concat_unit_seq_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ tail e₂ U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₂))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hHeadSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_is_non_empty tail) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁)) tail)
        (Term.Apply (Term.UOp UserOp.seq_unit) e₂) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_is_non_empty tail) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailNonEmpty⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact concat_seq_unit_seq_unit_model_eval_eq_false_of_head
      M hM e₁ tail e₂ hLeftTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact concat_seq_unit_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ tail e₂ hLeftTrans hTailNonEmpty

private theorem seq_distinct_seq_unit_concat_unit_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M)
    (e₁ e₂ tail U : Term) :
    RuleProofs.eo_has_smt_translation
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    (__eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) U =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e₁)))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail))) =
      SmtValue.Boolean false := by
  intro hRightTrans hHeadSound hDistinct
  have hBranch :
      __eo_ite
          (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
            (__are_distinct_terms_type e₁ e₂ U))
          (Term.Boolean true) (__seq_is_non_empty tail) =
        Term.Boolean true := by
    change __seq_distinct_terms
        (Term.Apply (Term.UOp UserOp.seq_unit) e₁)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂)) tail) U =
      Term.Boolean true at hDistinct
    cases U <;>
      (rw [__seq_distinct_terms.eq_def] at hDistinct
       simp only at hDistinct)
    all_goals first | exact hDistinct | cases hDistinct
  rcases eo_ite_eq_true_cases
      (__eo_ite (__eo_eq e₁ e₂) (Term.Boolean false)
        (__are_distinct_terms_type e₁ e₂ U))
      (Term.Boolean true) (__seq_is_non_empty tail) hBranch with
    ⟨hHeadGuard, _⟩ | ⟨_hHeadGuardFalse, hTailNonEmpty⟩
  · rcases eo_ite_eq_false_guard_true hHeadGuard with
      ⟨hHeadEqFalse, hHeadDistinct⟩
    exact seq_unit_concat_seq_unit_model_eval_eq_false_of_head
      M hM e₁ e₂ tail hRightTrans
      (hHeadSound hHeadEqFalse hHeadDistinct)
  · exact seq_unit_concat_seq_unit_model_eval_eq_false_of_tail
      M hM e₁ e₂ tail hRightTrans hTailNonEmpty

private theorem seq_distinct_terms_model_eval_eq_false_of_head_sound
    (M : SmtModel) (hM : model_total_typed M) (a b U : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (∀ e₁ e₂,
      RuleProofs.eo_has_smt_translation e₁ ->
      RuleProofs.eo_has_smt_translation e₂ ->
      __eo_eq e₁ e₂ = Term.Boolean false ->
      __are_distinct_terms_type e₁ e₂ U = Term.Boolean true ->
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt e₁))
          (__smtx_model_eval M (__eo_to_smt e₂)) =
        SmtValue.Boolean false) ->
    __seq_distinct_terms a b U = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hHeadSound hDistinct
  by_cases hbEmpty :
      ∃ V, b = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
  · rcases hbEmpty with ⟨V, rfl⟩
    exact seq_distinct_terms_right_empty_model_eval_eq_false
      M hM a V U haTrans hbTrans hDistinct
  · by_cases haEmpty :
        ∃ V, a = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)
    · rcases haEmpty with ⟨V, rfl⟩
      exact seq_distinct_terms_left_empty_model_eval_eq_false
        M hM V b U haTrans hbTrans hDistinct
    · by_cases hConcatConcat :
        ∃ e₁ tail₁ e₂ tail₂,
          a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ ∧
          b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂
      · rcases hConcatConcat with ⟨e₁, tail₁, e₂, tail₂, hA, hB⟩
        subst a
        subst b
        have hLeftArgs :=
          str_concat_arg_translations_of_translation
            (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ haTrans
        have hRightArgs :=
          str_concat_arg_translations_of_translation
            (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂ hbTrans
        have he₁Trans :
            RuleProofs.eo_has_smt_translation e₁ :=
          seq_unit_arg_translation_of_translation e₁ hLeftArgs.1
        have he₂Trans :
            RuleProofs.eo_has_smt_translation e₂ :=
          seq_unit_arg_translation_of_translation e₂ hRightArgs.1
        have hTailMeasure :
            sizeOf tail₁ + sizeOf tail₂ <
              sizeOf (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁) +
                sizeOf (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) := by
          simp [mkConcat]
          omega
        exact seq_distinct_concat_unit_concat_unit_model_eval_eq_false
          M hM e₁ tail₁ e₂ tail₂ U haTrans hbTrans
          (fun hEq hHeadDistinct =>
            hHeadSound e₁ e₂ he₁Trans he₂Trans hEq hHeadDistinct)
          (fun hTailDistinct =>
            seq_distinct_terms_model_eval_eq_false_of_head_sound
              M hM tail₁ tail₂ U hLeftArgs.2 hRightArgs.2
              hHeadSound hTailDistinct)
          hDistinct
      · by_cases hConcatUnit :
          ∃ e₁ tail e₂,
            a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail ∧
            b = Term.Apply (Term.UOp UserOp.seq_unit) e₂
        · rcases hConcatUnit with ⟨e₁, tail, e₂, hA, hB⟩
          subst a
          subst b
          have hLeftArgs :=
            str_concat_arg_translations_of_translation
              (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail haTrans
          have he₁Trans :
              RuleProofs.eo_has_smt_translation e₁ :=
            seq_unit_arg_translation_of_translation e₁ hLeftArgs.1
          have he₂Trans :
              RuleProofs.eo_has_smt_translation e₂ :=
            seq_unit_arg_translation_of_translation e₂ hbTrans
          exact seq_distinct_concat_unit_seq_unit_model_eval_eq_false
            M hM e₁ tail e₂ U haTrans
            (fun hEq hHeadDistinct =>
              hHeadSound e₁ e₂ he₁Trans he₂Trans hEq hHeadDistinct)
            hDistinct
        · by_cases hUnitConcat :
            ∃ e₁ e₂ tail,
              a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
              b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail
          · rcases hUnitConcat with ⟨e₁, e₂, tail, hA, hB⟩
            subst a
            subst b
            have hRightArgs :=
              str_concat_arg_translations_of_translation
                (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail hbTrans
            have he₁Trans :
                RuleProofs.eo_has_smt_translation e₁ :=
              seq_unit_arg_translation_of_translation e₁ haTrans
            have he₂Trans :
                RuleProofs.eo_has_smt_translation e₂ :=
              seq_unit_arg_translation_of_translation e₂ hRightArgs.1
            exact seq_distinct_seq_unit_concat_unit_model_eval_eq_false
              M hM e₁ e₂ tail U hbTrans
              (fun hEq hHeadDistinct =>
                hHeadSound e₁ e₂ he₁Trans he₂Trans hEq hHeadDistinct)
              hDistinct
          · by_cases hUnitUnit :
              ∃ e₁ e₂,
                a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
                b = Term.Apply (Term.UOp UserOp.seq_unit) e₂
            · rcases hUnitUnit with ⟨e₁, e₂, hA, hB⟩
              subst a
              subst b
              have he₁Trans :
                  RuleProofs.eo_has_smt_translation e₁ :=
                seq_unit_arg_translation_of_translation e₁ haTrans
              have he₂Trans :
                  RuleProofs.eo_has_smt_translation e₂ :=
                seq_unit_arg_translation_of_translation e₂ hbTrans
              exact seq_distinct_seq_unit_seq_unit_model_eval_eq_false
                M e₁ e₂ U
                (fun hEq hHeadDistinct =>
                  hHeadSound e₁ e₂ he₁Trans he₂Trans hEq hHeadDistinct)
                hDistinct
            · -- All remaining shapes make `__seq_distinct_terms` false or stuck.
              sorry
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals try assumption
  all_goals simp_all [mkConcat]
  all_goals omega

private theorem eo_typeof_eq_bool_operands_eq {A B : Term} :
    __eo_typeof_eq A B = Term.Bool -> A = B := by
  intro h
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h hA
  have hDef :
      __eo_typeof_eq A B =
        __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
    cases A <;> cases B <;> simp [__eo_typeof_eq] at hA hB ⊢
  have hReq :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool = Term.Bool := by
    simpa [hDef] using h
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReq]
    intro hBad
    cases hBad
  exact eo_eq_true_eq (eo_requires_arg_eq_of_ne_stuck hReqNe)

private theorem eo_typeof_not_eq_bool_operands_eq {a b : Term} :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
      Term.Bool ->
    __eo_typeof a = __eo_typeof b := by
  intro h
  change __eo_typeof_not
      (__eo_typeof_eq (__eo_typeof a) (__eo_typeof b)) = Term.Bool at h
  cases hEqTy : __eo_typeof_eq (__eo_typeof a) (__eo_typeof b) <;>
    simp [__eo_typeof_not, hEqTy] at h
  exact eo_typeof_eq_bool_operands_eq hEqTy

private theorem eq_has_bool_type_of_not_eq_typeof_bool
    (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro haTrans hbTrans hTy
  have hEoTy : __eo_typeof a = __eo_typeof b :=
    eo_typeof_not_eq_bool_operands_eq hTy
  have haSmtTy :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    (TranslationProofs.eo_to_smt_type_typeof_of_smt_type a rfl haTrans).symm
  have hbSmtTy :
      __smtx_typeof (__eo_to_smt b) = __eo_to_smt_type (__eo_typeof b) :=
    (TranslationProofs.eo_to_smt_type_typeof_of_smt_type b rfl hbTrans).symm
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [haSmtTy, hbSmtTy, hEoTy]
  · exact haTrans

private theorem prog_distinct_values_shape_of_ne_stuck {a b : Term} :
    __eo_prog_distinct_values a b ≠ Term.Stuck ->
    __eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a)) =
      Term.Boolean true ∧
    __eo_prog_distinct_values a b =
      Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro hProg
  cases a <;> cases b <;>
    try
      (change Term.Stuck ≠ Term.Stuck at hProg
       exact False.elim (hProg rfl))
  all_goals
    constructor
    · exact eo_requires_arg_eq_of_ne_stuck hProg
    · exact eo_requires_result_eq_of_ne_stuck hProg

private theorem prog_distinct_values_shape_of_typeof_bool {a b : Term} :
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    __eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a)) =
      Term.Boolean true ∧
    __eo_prog_distinct_values a b =
      Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro hTy
  exact prog_distinct_values_shape_of_ne_stuck
    (term_ne_stuck_of_typeof_bool hTy)

private theorem typed___eo_prog_distinct_values_impl
    (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_distinct_values a b) := by
  intro haTrans hbTrans hTy
  rcases prog_distinct_values_shape_of_typeof_bool hTy with
    ⟨_hGuard, hProgEq⟩
  have hBodyTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    eq_has_bool_type_of_not_eq_typeof_bool a b haTrans hbTrans hBodyTy
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_not_of_bool_arg
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hEqBool

private theorem facts___eo_prog_distinct_values_of_eval_eq_false
    (M : SmtModel) (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false ->
    eo_interprets M (__eo_prog_distinct_values a b) true := by
  intro haTrans hbTrans hTy hEvalEqFalse
  rcases prog_distinct_values_shape_of_typeof_bool hTy with
    ⟨_hGuard, hProgEq⟩
  have hBodyTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    eq_has_bool_type_of_not_eq_typeof_bool a b haTrans hbTrans hBodyTy
  have hEqFalse :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false := by
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hEqBool
    · change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Boolean false
      simp [__smtx_model_eval, hEvalEqFalse]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_not_of_false M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hEqFalse

private theorem are_distinct_terms_type_model_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_eq a b = Term.Boolean false ->
    __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false := by
  intro haTrans hbTrans hEqFalse hDistinct
  cases hTy : __eo_typeof a with
  | UOp op =>
      cases op <;> try
        (exact are_distinct_terms_type_primitive_model_eval_eq_false
          M a b (Term.UOp op) hEqFalse (by simpa [hTy] using hDistinct)
          (by simp))
      all_goals
        -- Non-primitive type heads fall through to the datatype recognizer.
        sorry
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              exact are_distinct_terms_type_primitive_model_eval_eq_false
                M a b (Term.Apply (Term.UOp UserOp.BitVec) x)
                hEqFalse (by simpa [hTy] using hDistinct)
                (by simp)
          | Seq =>
              by_cases hxChar : x = Term.UOp UserOp.Char
              · subst x
                exact are_distinct_terms_type_primitive_model_eval_eq_false
                  M a b
                  (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                  hEqFalse (by simpa [hTy] using hDistinct)
                  (by simp)
              · have hSeqDistinct :
                    __seq_distinct_terms a b x = Term.Boolean true := by
                  apply are_distinct_terms_type_seq_true_seq_distinct hxChar
                  simpa [hTy] using hDistinct
                exact seq_distinct_terms_model_eval_eq_false
                  M hM a b x haTrans hbTrans hEqFalse hSeqDistinct
          | Set =>
              have hSetWitness :
                  __set_is_not_subset a b x = Term.Boolean true ∨
                    __set_is_not_subset b a x = Term.Boolean true := by
                apply are_distinct_terms_type_set_true_not_subset
                simpa [hTy] using hDistinct
              rcases hSetWitness with hAB | hBA
              · by_cases hSingletonEmpty :
                  ∃ e U,
                    a = Term.Apply (Term.UOp UserOp.set_singleton) e ∧
                    b =
                      Term.UOp1 UserOp1.set_empty
                        (Term.Apply (Term.UOp UserOp.Set) U)
                · rcases hSingletonEmpty with ⟨e, U, rfl, rfl⟩
                  exact set_is_not_subset_singleton_empty_model_eval_eq_false
                    M e U x hbTrans hAB
                · -- Remaining set witnesses include singleton/singleton and unions.
                  sorry
              · by_cases hSingletonEmpty :
                  ∃ e U,
                    b = Term.Apply (Term.UOp UserOp.set_singleton) e ∧
                    a =
                      Term.UOp1 UserOp1.set_empty
                        (Term.Apply (Term.UOp UserOp.Set) U)
                · rcases hSingletonEmpty with ⟨e, U, rfl, rfl⟩
                  exact set_is_not_subset_singleton_empty_model_eval_eq_false_symm
                    M e U x haTrans hBA
                · -- Remaining set witnesses include singleton/singleton and unions.
                  sorry
          | _ =>
              -- Other applied type heads use datatype spine distinctness.
              sorry
      | _ =>
          -- Non-`UOp` type applications are datatype-style fallthroughs.
          sorry
  | Bool =>
      exact are_distinct_terms_type_primitive_model_eval_eq_false
        M a b Term.Bool hEqFalse (by simpa [hTy] using hDistinct)
        (by simp)
  | _ =>
      -- All other EO types use datatype spine distinctness.
      sorry

theorem cmd_step_distinct_values_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_values args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_values args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_values args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.distinct_values args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  let A1 := a1
                  let A2 := a2
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons A1 (CArgList.cons A2 CArgList.nil)) := by
                    simpa [cmdTranslationOk, A1, A2] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                    simpa [A1, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation A2 := by
                    simpa [A2, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.2.1
                  change __eo_typeof (__eo_prog_distinct_values A1 A2) =
                    Term.Bool at hResultTy
                  rcases prog_distinct_values_shape_of_typeof_bool hResultTy with
                    ⟨hGuardTrue, _hProgEq⟩
                  rcases eo_ite_eq_false_guard_true hGuardTrue with
                    ⟨hEqFalse, hDistinct⟩
                  have hEvalEqFalse :
                      __smtx_model_eval_eq
                        (__smtx_model_eval M (__eo_to_smt A1))
                        (__smtx_model_eval M (__eo_to_smt A2)) =
                        SmtValue.Boolean false := by
                    exact are_distinct_terms_type_model_eval_eq_false
                      M hM A1 A2 hA1Trans hA2Trans hEqFalse hDistinct
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_distinct_values A1 A2) true
                    exact facts___eo_prog_distinct_values_of_eval_eq_false
                      M A1 A2 hA1Trans hA2Trans hResultTy hEvalEqFalse
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_distinct_values A1 A2)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_distinct_values A1 A2)
                      (typed___eo_prog_distinct_values_impl
                        A1 A2 hA1Trans hA2Trans hResultTy)
