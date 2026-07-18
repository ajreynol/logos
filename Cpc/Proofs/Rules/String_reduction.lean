import Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- `seq.nth` at a natural index agrees with list `getD`. -/
private theorem sr_ssm_seq_nth_ofNat (d : SmtValue) :
    ∀ (s : SmtSeq) (j : Nat),
      __smtx_ssm_seq_nth s (Int.ofNat j) d =
        (native_unpack_seq s).getD j d
  | SmtSeq.empty T, j => by
      simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, 0 => by
      simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, (j + 1) => by
      have hidx :
          native_zplus (Int.ofNat (j + 1)) (native_zneg 1) =
            Int.ofNat j := by
        show Int.ofNat j + 1 + (-1) = Int.ofNat j
        omega
      have ih := sr_ssm_seq_nth_ofNat d vs j
      simp only [__smtx_ssm_seq_nth, hidx, ih, native_unpack_seq,
        List.getD_cons_succ]

/-- In bounds, the default supplied to `getD` is irrelevant. -/
private theorem sr_getD_lt_eq (d d' : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : l.getD j d = l.getD j d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some, Option.getD_some]

/-- Split a list immediately around an in-bounds element. -/
private theorem sr_take_getD_drop_succ
    (d : SmtValue) (l : List SmtValue) (j : Nat) (h : j < l.length) :
    l.take j ++ [l.getD j d] ++ l.drop (j + 1) = l := by
  induction l generalizing j with
  | nil => simp at h
  | cons a l ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa [List.take_succ_cons, List.getD_cons_succ,
            List.drop_succ_cons, Nat.succ_eq_add_one, Nat.add_assoc] using
            congrArg (fun xs => a :: xs) (ih j h)

private abbrev srMkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev srMkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private abbrev srPurify (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify) x

private abbrev stringReductionBody (s : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and) (__str_reduction_pred s))
    (srMkAnd (srMkEq s (srPurify s)) (Term.Boolean true))

/-- The purification marker is semantically the identity. -/
private theorem eo_interprets_purify_eq_self
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s) :
    eo_interprets M (srMkEq s (srPurify s)) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · exact hTrans
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt s)))
    simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
      RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt s))

/-- Once its generated predicate holds, the common string-reduction shell holds. -/
private theorem string_reduction_body_true
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hPred : eo_interprets M (__str_reduction_pred s) true) :
    eo_interprets M (stringReductionBody s) true := by
  have hPredNe : __str_reduction_pred s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hPred))
  simp only [stringReductionBody, __eo_mk_apply, hPredNe]
  apply RuleProofs.eo_interprets_and_intro M
  · exact hPred
  · apply RuleProofs.eo_interprets_and_intro M
    · exact eo_interprets_purify_eq_self M s hTrans
    · exact RuleProofs.eo_interprets_true M

/-- Semantic obligations specific to the individual string-reduction cases. -/
private theorem string_reduction_pred_true
    (M : SmtModel) (hM : model_total_typed M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hClosed : __eo_is_closed s = Term.Boolean true)
    (hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool) :
    eo_interprets M (__str_reduction_pred s) true := by
  cases s <;>
    simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
  all_goals try
    (change Term.Stuck = Term.Bool at hBodyTy
     exact False.elim (Term.noConfusion hBodyTy))
  case Apply f x =>
    cases f <;> try
      simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
    all_goals try
      (change Term.Stuck = Term.Bool at hBodyTy
       exact False.elim (Term.noConfusion hBodyTy))
    case UOp op =>
      cases op <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case str_from_int => sorry
      case str_to_int => sorry
      case str_to_lower => sorry
      case str_to_upper => sorry
      case str_rev =>
        have hOrigNN :
            term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) := by
          simpa [RuleProofs.eo_has_smt_translation] using hTrans
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
            (typeof_str_rev_eq (__eo_to_smt x)) hOrigNN with ⟨T, hxTy⟩
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none T
        have hTWf : __smtx_type_wf (SmtType.Seq T) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt x) hXNN hxTy
        have hRevTy :
            __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) =
              SmtType.Seq T := by
          rw [typeof_str_rev_eq, hxTy]
          simp [__smtx_typeof_seq_op_1, __smtx_typeof_guard_wf, hTWf,
            native_ite]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq T := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        have hElemTy : __smtx_elem_typeof_seq_value sx = T :=
          elem_typeof_seq_value_of_typeof_seq_value hSxTy
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          simpa [__eo_is_closed, __eo_is_closed_rec, __eo_and,
            native_and] using hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let revS := SmtTerm._at_purify (SmtTerm.str_rev (__eo_to_smt x))
        let revLen := SmtTerm.str_len revS
        let mirrorStart := SmtTerm.neg (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.plus idx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))
        let sliceEq := SmtTerm.eq
          (SmtTerm.str_substr revS idx (SmtTerm.Numeral 1))
          (SmtTerm.str_substr (__eo_to_smt x) mirrorStart
            (SmtTerm.Numeral 1))
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx revLen))
            (SmtTerm.or sliceEq (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) = SmtType.Bool
            simp [typeof_eq_eq, typeof_str_len_eq, hxTy, hRevTy,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq, native_ite,
              native_Teq, __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) =
                SmtValue.Boolean true
            simp [__smtx_model_eval, hXEval, __smtx_model_eval_str_len,
              __smtx_model_eval_str_rev, __smtx_model_eval__at_purify,
              __smtx_model_eval_eq, native_seq_len, native_seq_rev,
              Smtm.native_unpack_pack_seq, native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.forall idxName SmtType.Int qBody) = SmtType.Bool
              simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                smtx_typeof_forall_term_eq, typeof_or_eq, typeof_not_eq,
                typeof_geq_eq, typeof_lt_eq, typeof_eq_eq,
                typeof_str_len_eq, typeof_str_substr_eq, typeof_neg_eq,
                typeof_plus_eq, hxTy, hRevTy, __smtx_typeof,
                __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf,
                native_ite, native_Teq]
            · change native_eval_tforall M idxName SmtType.Int qBody =
                SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical_bool v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                simp [qBody, sliceEq, mirrorStart, revLen, revS, idx, Mk,
                  __smtx_model_eval, hXEvalPush, native_model_var_lookup,
                  native_model_push, __smtx_model_eval_or,
                  __smtx_model_eval_not, __smtx_model_eval_geq,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  __smtx_model_eval_eq, __smtx_model_eval_str_len,
                  __smtx_model_eval_str_rev, __smtx_model_eval_str_substr,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, native_seq_len, native_seq_rev,
                  native_zleq, native_zlt, native_zplus, native_zneg,
                  native_and, native_or, native_not,
                  Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  hElemTy, native_veq]
              simpa [native_eval_tforall, hAll]
          · exact RuleProofs.eo_interprets_true M
    case Apply g y =>
      cases g <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case UOp op =>
        cases op <;> try
          simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
        all_goals try
          (change Term.Stuck = Term.Bool at hBodyTy
           exact False.elim (Term.noConfusion hBodyTy))
        case str_contains => sorry
        case seq_nth =>
          have hOrigNN :
              term_has_non_none_type
                (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
            simpa [RuleProofs.eo_has_smt_translation] using hTrans
          rcases seq_nth_args_of_non_none hOrigNN with ⟨T, hyTy, hxTy⟩
          let pre := srPurify
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) y)
                (Term.Numeral 0)) x)
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
            change __smtx_typeof
                (SmtTerm._at_purify
                  (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                    (__eo_to_smt x))) = SmtType.Seq T
            simp [__smtx_typeof, typeof_str_substr_eq, hyTy, hxTy,
              __smtx_typeof_str_substr, native_ite, native_Teq]
          have hNilNe :
              __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                Term.Stuck :=
            nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
          have hNilNe' :
              __eo_nil (Term.UOp UserOp.str_concat)
                  (__eo_typeof
                    (srPurify
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_substr) y)
                          (Term.Numeral 0)) x))) ≠
                Term.Stuck := by
            simpa [pre] using hNilNe
          simp only [hNilNe', __eo_mk_apply] at hBodyTy ⊢
          have hTWf : __smtx_type_wf T = true :=
            (smt_seq_component_wf_of_non_none_type (__eo_to_smt y) T hyTy).2
          have hYNN : term_has_non_none_type (__eo_to_smt y) := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none T
          have hSeqTWf : __smtx_type_wf (SmtType.Seq T) = true :=
            Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt y) hYNN hyTy
          have hNthTy :
              __smtx_typeof
                  (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) = T := by
            rw [typeof_seq_nth_eq, hyTy, hxTy]
            simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hTWf,
              native_ite]
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let len := SmtTerm.str_len ty
          let next := SmtTerm.plus tx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
          let remaining := SmtTerm.neg len next
          let preS := SmtTerm._at_purify
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) tx)
          let nthS := SmtTerm._at_purify (SmtTerm.seq_nth ty tx)
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty next remaining)
          let nilS := __eo_to_smt
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
          let decomposition := SmtTerm.str_concat preS
            (SmtTerm.str_concat (SmtTerm.seq_unit nthS)
              (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.and (SmtTerm.geq tx (SmtTerm.Numeral 0))
            (SmtTerm.and (SmtTerm.gt len tx) (SmtTerm.Boolean true))
          let rhs := SmtTerm.and (SmtTerm.eq ty decomposition)
            (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tx)
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len suffixS) remaining)
                (SmtTerm.Boolean true)))
          have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
            simpa [nilS, pre] using
              smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
          have hLenTy : __smtx_typeof len = SmtType.Int := by
            simp [len, ty, typeof_str_len_eq, hyTy,
              __smtx_typeof_seq_op_1_ret]
          have hNextTy : __smtx_typeof next = SmtType.Int := by
            simp [next, tx, hxTy, typeof_plus_eq,
              __smtx_typeof_arith_overload_op_2, __smtx_typeof]
          have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
            simp [remaining, hLenTy, hNextTy, typeof_neg_eq,
              __smtx_typeof_arith_overload_op_2]
          have hPreSTy : __smtx_typeof preS = SmtType.Seq T := by
            simpa [preS, ty, tx, pre] using hPreTy
          have hNthSTy : __smtx_typeof nthS = T := by
            simpa [nthS, ty, tx, __smtx_typeof] using hNthTy
          have hSuffixTy : __smtx_typeof suffixS = SmtType.Seq T := by
            change __smtx_typeof (SmtTerm.str_substr ty next remaining) =
              SmtType.Seq T
            simp [typeof_str_substr_eq, ty, hNextTy, hRemainingTy, hyTy,
              __smtx_typeof_str_substr]
          have hUnitTy :
              __smtx_typeof (SmtTerm.seq_unit nthS) = SmtType.Seq T := by
            rw [smtx_typeof_seq_unit_term_eq, hNthSTy]
            simp [__smtx_typeof_guard_wf, hSeqTWf, native_ite]
          have hDecompositionTy :
              __smtx_typeof decomposition = SmtType.Seq T := by
            simp [decomposition, typeof_str_concat_eq, hPreSTy, hUnitTy,
              hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
              native_Teq]
          have hCondTy : __smtx_typeof cond = SmtType.Bool := by
            simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq, hLenTy,
              tx, hxTy, __smtx_typeof_arith_overload_op_2_ret,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
            simp [rhs, typeof_and_eq, typeof_eq_eq, typeof_str_len_eq, ty,
              tx, hyTy, hxTy, hDecompositionTy, hPreSTy, hSuffixTy,
              hRemainingTy, __smtx_typeof_seq_op_1_ret,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof (SmtTerm.imp cond rhs) = SmtType.Bool
            simp [typeof_imp_eq, hCondTy, hRhsTy, __smtx_typeof_guard,
              native_ite, native_Teq]
          · change __smtx_model_eval M (SmtTerm.imp cond rhs) =
              SmtValue.Boolean true
            have hYValTy :
                __smtx_typeof_value (__smtx_model_eval M ty) =
                  SmtType.Seq T := by
              simpa [ty, hyTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt y) hYNN
            rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
            have hXNN : term_has_non_none_type tx := by
              unfold term_has_non_none_type
              rw [show __smtx_typeof tx = SmtType.Int by simpa [tx] using hxTy]
              decide
            have hXValTy :
                __smtx_typeof_value (__smtx_model_eval M tx) =
                  SmtType.Int := by
              simpa [tx, hxTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt x) (by simpa [tx] using hXNN)
            rcases int_value_canonical hXValTy with ⟨i, hXEval⟩
            have hNilEval :
                __smtx_model_eval M nilS = SmtValue.Seq (SmtSeq.empty T) := by
              simpa [nilS, pre] using
                eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
            have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
              simpa [hYEval, __smtx_typeof_value] using hYValTy
            have hElemTy : __smtx_elem_typeof_seq_value sy = T :=
              elem_typeof_seq_value_of_typeof_seq_value hSyTy
            rw [smtx_eval_imp_term_eq]
            simp [cond, rhs, decomposition, suffixS, nthS, preS, remaining,
              next, len, __smtx_model_eval, __smtx_model_eval_imp,
              __smtx_model_eval_and, __smtx_model_eval_eq,
              __smtx_model_eval_geq, __smtx_model_eval_gt,
              __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
              __smtx_model_eval_str_concat, __smtx_model_eval__at_purify,
              __smtx_model_eval_plus, __smtx_model_eval__,
              hYEval, hXEval, hNilEval, native_seq_len, native_seq_concat,
              native_and, native_or, native_not, native_zleq, native_zlt,
              native_zplus, native_zneg]
            by_cases hi : 0 ≤ i
            · by_cases hlt : i < Int.ofNat (native_unpack_seq sy).length
              · let xs := native_unpack_seq sy
                let j := Int.toNat i
                have hCast : Int.ofNat j = i := by
                  simpa [j] using Int.toNat_of_nonneg hi
                have hjlt : j < xs.length := by
                  have hlt' := hlt
                  rw [← hCast] at hlt'
                  exact Int.ofNat_lt.mp (by simpa [xs] using hlt')
                have hjSuccLe : j + 1 ≤ xs.length := by omega
                have hNextCast : i + 1 = Int.ofNat (j + 1) := by
                  rw [← hCast]
                  simp
                have hRemainingCast :
                    Int.ofNat xs.length + -(i + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  rw [hNextCast]
                  simpa using (Int.ofNat_sub hjSuccLe).symm
                have hRemainingNatCast :
                    Int.ofNat xs.length + -Int.ofNat (j + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  simpa using (Int.ofNat_sub hjSuccLe).symm
                have hPreExtract :
                    native_seq_extract xs 0 i = xs.take j := by
                  rw [← hCast]
                  exact native_seq_extract_zero_nat xs j (Nat.le_of_lt hjlt)
                have hSuffixExtract :
                    native_seq_extract xs (i + 1)
                        (Int.ofNat xs.length + -(i + 1)) =
                      xs.drop (j + 1) := by
                  rw [hNextCast, hRemainingNatCast]
                  exact native_seq_extract_to_end_nat xs (j + 1) hjSuccLe
                have hNthEval :
                    __smtx_seq_nth M (SmtValue.Seq sy) (SmtValue.Numeral i) =
                      xs.getD j SmtValue.NotValue := by
                  simp only [__smtx_seq_nth]
                  rw [← hCast, sr_ssm_seq_nth_ofNat]
                  exact sr_getD_lt_eq _ _ _ _ hjlt
                have hDecomp :
                    native_seq_extract xs 0 i ++
                        [__smtx_seq_nth M (SmtValue.Seq sy)
                          (SmtValue.Numeral i)] ++
                        native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1)) = xs := by
                  rw [hPreExtract, hNthEval, hSuffixExtract]
                  exact sr_take_getD_drop_succ SmtValue.NotValue xs j hjlt
                have hPreLen :
                    Int.ofNat (native_seq_extract xs 0 i).length = i := by
                  rw [hPreExtract, List.length_take,
                    Nat.min_eq_left (Nat.le_of_lt hjlt), hCast]
                have hSuffixLen :
                    Int.ofNat
                        (native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1))).length =
                      Int.ofNat xs.length + -(i + 1) := by
                  rw [hSuffixExtract, List.length_drop, hRemainingCast]
                have hPack : native_pack_seq T xs = sy := by
                  rw [← hElemTy]
                  exact native_pack_unpack_seq sy
                simp only [__smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, decide_eq_true_eq.mpr hi,
                  decide_eq_true_eq.mpr hlt, native_and, native_not,
                  __smtx_model_eval_not, __smtx_model_eval_or]
                simp only [Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  native_unpack_seq]
                simp [xs] at hDecomp hPreLen hSuffixLen hPack
                simp [hElemTy, hDecomp, hPreLen, hSuffixLen, hPack,
                  native_veq, native_and, native_or]
              · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, native_and, native_not,
                  native_or, hi, hlt, Int.le_of_not_gt hlt]
                exact Or.inl (Int.le_of_not_gt hlt)
            · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                __smtx_model_eval_leq, __smtx_model_eval_lt, native_zleq,
                native_zlt, native_and, native_not, native_or, hi]
        case str_leq => sorry
      case Apply h z =>
        sorry

/-- The complete generated result is true whenever its guard succeeds. -/
private theorem string_reduction_true
    (M : SmtModel) (hM : model_total_typed M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (__eo_prog_string_reduction s) = Term.Bool) :
    eo_interprets M (__eo_prog_string_reduction s) true := by
  have hProg : __eo_prog_string_reduction s ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hsNe : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hTrans
  have hProgEq :
      __eo_prog_string_reduction s =
        __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) := by
    cases s <;> simp [__eo_prog_string_reduction, stringReductionBody] at hsNe ⊢
  have hReqNe :
      __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) ≠ Term.Stuck := by
    simpa [hProgEq] using hProg
  have hReduce :
      __eo_prog_string_reduction s = stringReductionBody s := by
    rw [hProgEq]
    exact eo_requires_eq_result_of_ne_stuck _ _ _ hReqNe
  have hClosedRec :
      __is_closed_rec s Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck _ _ _ hReqNe
  have hClosed : __eo_is_closed s = Term.Boolean true := by
    cases s <;> simp [__eo_is_closed] at hsNe hClosedRec ⊢
    all_goals exact hClosedRec
  have hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool := by
    simpa [hReduce] using hTy
  rw [hReduce]
  exact string_reduction_body_true M s hTrans
    (string_reduction_pred_true M hM s hTrans hClosed hBodyTy)

theorem cmd_step_string_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.string_reduction args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons _ _ =>
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              exact False.elim (hProg rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
                  hCmdTrans.1
              have hTrue : eo_interprets M (__eo_prog_string_reduction a) true := by
                exact string_reduction_true M hM a hATrans hResultTy
              refine ⟨?_, ?_⟩
              · intro _
                exact hTrue
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue)
