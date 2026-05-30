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

private theorem native_pack_seq_ne_of_length_ne
    (T U : SmtType) {xs ys : List SmtValue}
    (hLen : xs.length ≠ ys.length) :
    native_pack_seq T xs ≠ native_pack_seq U ys := by
  intro hEq
  have hUnpack := congrArg native_unpack_seq hEq
  have hLenEq := congrArg List.length hUnpack
  apply hLen
  simpa [Smtm.native_unpack_pack_seq] using hLenEq

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
                    -- Remaining core: recursive soundness of
                    -- `__are_distinct_terms_type` for sets, sequences, and
                    -- datatype constructor spines.
                    sorry
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
