import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem seq_eval_op_shape {t u : Term}
    (h :
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠
        Term.Stuck) :
    __seq_eval t = u ∧
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u := by
  change __eo_requires (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠ Term.Stuck at h
  exact ⟨eo_requires_eq_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h,
    eo_requires_eq_result_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h⟩

private theorem term_ne_stuck_of_eo_is_list_true (f x : Term)
    (h : __eo_is_list f x = Term.Boolean true) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_is_list] at h

private theorem eo_list_concat_str_concat_lists_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hA := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hZ := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  exact ⟨hA, hZ⟩

private theorem eo_list_concat_str_concat_eq_rec_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hOuter := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInner := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hOuter, hInner]

private theorem str_value_len_numeral_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    ∃ n : native_Int, __str_value_len x = Term.Numeral n := by
  induction x using __str_value_len.induct with
  | case1 =>
      simp [__str_value_len] at h
  | case2 e ss ih =>
      change __eo_add (Term.Numeral 1) (__str_value_len ss) ≠ Term.Stuck at h
      have hTailNe : __str_value_len ss ≠ Term.Stuck := by
        intro hTail
        rw [hTail] at h
        simp [__eo_add] at h
      rcases ih hTailNe with ⟨n, hn⟩
      change ∃ m : native_Int,
        __eo_add (Term.Numeral 1) (__str_value_len ss) = Term.Numeral m
      rw [hn]
      simp [__eo_add, native_zplus]
  | case3 T =>
      exact ⟨0, by simp [__str_value_len]⟩
  | case4 e =>
      exact ⟨1, by simp [__str_value_len]⟩
  | case5 s hs1 hs2 hs3 =>
      cases s <;>
        simp [__str_value_len, __eo_requires, __eo_is_str,
          __eo_is_str_internal, __eo_len, native_ite, native_teq,
          SmtEval.native_and, SmtEval.native_not] at h ⊢

private theorem str_value_len_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_value_len] at h

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem str_len_int_eval_of_seq_eval
    (M : SmtModel) (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
  intro hSEval
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length)
  rw [smtx_eval_str_len_term_eq, hSEval]
  simp [__smtx_model_eval_str_len, native_seq_len]

private theorem smt_value_rel_model_eval_str_len_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_len a) (__smtx_model_eval_str_len b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_len, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem str_value_len_eval_seq_length
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ x T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ->
      __str_value_len x ≠ Term.Stuck ->
      ∃ sx n,
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
          __str_value_len x = Term.Numeral n ∧
          n = Int.ofNat (native_unpack_seq sx).length := by
  intro x
  induction x using __str_value_len.induct with
  | case1 =>
      intro T hxTy _hLenNe
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hxTy
      rw [TranslationProofs.smtx_typeof_none] at hxTy
      cases hxTy
  | case2 e ss ih =>
      intro T hxTy hLenNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      have hTailNe : __str_value_len ss ≠ Term.Stuck := by
        intro hTail
        change __eo_add (Term.Numeral 1) (__str_value_len ss) ≠
          Term.Stuck at hLenNe
        rw [hTail] at hLenNe
        simp [__eo_add] at hLenNe
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ss T (by simpa [head] using hxTy)
      obtain ⟨stail, ntail, hTailEval, hTailLen, hNtail⟩ :=
        ih T hTailTy hTailNe
      obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
      obtain ⟨sxy, hWholeEval, hWholeUnp⟩ :=
        RuleProofs.concat_unpack M head ss shead stail hHeadEval hTailEval
      refine ⟨sxy, native_zplus (1 : native_Int) ntail,
        by simpa [head] using hWholeEval, ?_, ?_⟩
      · change __eo_add (Term.Numeral 1) (__str_value_len ss) =
          Term.Numeral (native_zplus (1 : native_Int) ntail)
        rw [hTailLen]
        simp [__eo_add]
      · rw [hWholeUnp, hHeadUnp, hNtail]
        simp [native_zplus]
        exact Int.add_comm 1 (Int.ofNat (native_unpack_seq stail).length)
  | case3 U =>
      intro T hxTy _hLenNe
      change __smtx_typeof
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtType.Seq T at hxTy
      refine ⟨SmtSeq.empty T, 0, ?_, by simp [__str_value_len], ?_⟩
      · change __smtx_model_eval M
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
          SmtValue.Seq (SmtSeq.empty T)
        cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) with
        | Seq A =>
            simp [__eo_to_smt_seq_empty, hTy] at hxTy ⊢
            rw [smtx_typeof_seq_empty_term_eq] at hxTy
            have hGuardNN :
                __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
                  SmtType.None := by
              rw [hxTy]
              exact seq_ne_none T
            have hGuard :
                __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) =
                  SmtType.Seq A :=
              smtx_typeof_guard_wf_of_non_none (SmtType.Seq A)
                (SmtType.Seq A) hGuardNN
            rw [hGuard] at hxTy
            injection hxTy with hA
            subst A
            rw [smtx_eval_seq_empty_term_eq]
        | _ =>
            simp [__eo_to_smt_seq_empty, hTy,
              TranslationProofs.smtx_typeof_none] at hxTy
      · simp [native_unpack_seq]
  | case4 e =>
      intro T hxTy _hLenNe
      obtain ⟨sa, hEval, hUnp⟩ := RuleProofs.eval_seqUnitAtom M e
      refine ⟨sa, 1, hEval, by simp [__str_value_len], ?_⟩
      rw [hUnp]
      simp
  | case5 s hs1 hs2 hs3 =>
      intro T hxTy hLenNe
      cases s <;>
        simp [__str_value_len, __eo_requires, __eo_is_str,
          __eo_is_str_internal, __eo_len, native_ite, native_teq,
          SmtEval.native_and, SmtEval.native_not] at hLenNe ⊢
      case String a h4 =>
        refine ⟨native_pack_string a, ?_, ?_⟩
        · change __smtx_model_eval M (SmtTerm.String a) =
            SmtValue.Seq (native_pack_string a)
          rw [__smtx_model_eval.eq_4]
        · rw [RuleProofs.unpack_pack_string_map]
          simp [native_str_len]

private theorem seq_eval_smt_type_and_value_rel
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ t,
      __seq_eval t ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (__seq_eval t)) =
          __smtx_typeof (__eo_to_smt t) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
          (__smtx_model_eval M (__eo_to_smt t)) := by
  intro t hEvalNe hNN
  induction t using __seq_eval.induct with
  | case1 =>
      simp [__seq_eval] at hEvalNe
  | case2 t n =>
      sorry
  | case3 t =>
      have hLenNe : __str_value_len (__str_nary_intro t) ≠ Term.Stuck := by
        simpa [__seq_eval] using hEvalNe
      rcases str_value_len_numeral_of_ne_stuck (__str_nary_intro t) hLenNe with
        ⟨n, hLen⟩
      have hLenTermNN :
          term_has_non_none_type (SmtTerm.str_len (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        simpa using hNN
      rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
          (typeof_str_len_eq (__eo_to_smt t)) hLenTermNN with
        ⟨T, htTy⟩
      constructor
      · change
          __smtx_typeof (__eo_to_smt (__str_value_len (__str_nary_intro t))) =
            __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        rw [hLen]
        change __smtx_typeof (SmtTerm.Numeral n) =
          __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        have hNumTy : __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int := by
          rw [__smtx_typeof.eq_2]
        rw [hNumTy]
        rw [typeof_str_len_eq]
        simp [__smtx_typeof_seq_op_1_ret, htTy]
      · have hIntroNe : __str_nary_intro t ≠ Term.Stuck :=
          str_value_len_arg_ne_stuck_of_ne_stuck (__str_nary_intro t) hLenNe
        have hTComponents :
            type_inhabited T ∧ __smtx_type_wf T = true := by
          have hSeqWF :
              __smtx_type_wf (SmtType.Seq T) = true := by
            have hGood :=
              smt_term_result_seq_components_wf_of_non_none
                (__eo_to_smt t)
                (by
                  unfold term_has_non_none_type
                  rw [htTy]
                  exact seq_ne_none T)
            simpa [htTy, type_result_seq_components_wf] using hGood
          exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
        have hIntroNN :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
              SmtType.None :=
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 hIntroNe
        have hIntroTy :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) =
              SmtType.Seq T :=
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            hIntroNN hIntroNe
        obtain ⟨sIntro, nIntro, hIntroEval, hIntroLen, hNIntro⟩ :=
          str_value_len_eval_seq_length M hM (__str_nary_intro t) T
            hIntroTy hLenNe
        have hLenIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (__str_value_len (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t)))) := by
          rw [hIntroLen]
          have hNumEval :
              __smtx_model_eval M (__eo_to_smt (Term.Numeral nIntro)) =
                SmtValue.Numeral nIntro := by
            change __smtx_model_eval M (SmtTerm.Numeral nIntro) =
              SmtValue.Numeral nIntro
            rw [__smtx_model_eval.eq_2]
          rw [hNumEval]
          change RuleProofs.smt_value_rel
            (SmtValue.Numeral nIntro)
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
          rw [smtx_eval_str_len_term_eq, hIntroEval]
          rw [hNIntro]
          simp [__smtx_model_eval_str_len, native_seq_len,
            RuleProofs.smt_value_rel_refl]
        have hIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy hIntroNe
        have hLenCongRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t))) := by
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
            (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)))
          rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq]
          exact smt_value_rel_model_eval_str_len_of_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
            (__smtx_model_eval M (__eo_to_smt t)) hIntroRel
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M
            (__eo_to_smt (__str_value_len (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp.str_len) (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t)))
          hLenIntroRel hLenCongRel
  | case4 t ts ih =>
      have hConcatNN :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)) ≠
            SmtType.None := hNN
      rcases str_concat_args_of_non_none t ts hConcatNN with
        ⟨T, htTy, htsTy⟩
      let a := __str_nary_intro t
      let z := __str_nary_intro (__seq_eval ts)
      let c := __eo_list_concat (Term.UOp UserOp.str_concat) a z
      have hCNe : c ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck c
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hLists :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true :=
        eo_list_concat_str_concat_lists_of_ne_stuck a z hCNe
      have hIntroTNe : a ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) a hLists.1
      have hIntroEvalTsNe : z ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) z hLists.2
      have hSeqEvalTsNe : __seq_eval ts ≠ Term.Stuck := by
        exact str_nary_intro_arg_ne_stuck_of_ne_stuck (__seq_eval ts)
          (by simpa [z] using hIntroEvalTsNe)
      have htsNN : __smtx_typeof (__eo_to_smt ts) ≠ SmtType.None := by
        rw [htsTy]
        exact seq_ne_none T
      rcases ih hSeqEvalTsNe htsNN with
        ⟨hSeqEvalTsTySame, hSeqEvalTsRel⟩
      have hSeqEvalTsTy :
          __smtx_typeof (__eo_to_smt (__seq_eval ts)) = SmtType.Seq T := by
        rw [hSeqEvalTsTySame, htsTy]
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
          (by
            simpa [a] using
              str_nary_intro_has_smt_translation_of_seq_wf t T htTy
                hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe))
          (by simpa [a] using hIntroTNe)
      have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck (__seq_eval ts) T
          hSeqEvalTsTy
          (by
            simpa [z] using
              str_nary_intro_has_smt_translation_of_seq_wf (__seq_eval ts) T
                hSeqEvalTsTy hTComponents.1 hTComponents.2
                (by simpa [z] using hIntroEvalTsNe))
          (by simpa [z] using hIntroEvalTsNe)
      have hCEqRec :
          c = __eo_list_concat_rec a z :=
        eo_list_concat_str_concat_eq_rec_of_ne_stuck a z hCNe
      have hRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
            SmtType.Seq T :=
        smt_typeof_list_concat_rec_str_concat_of_seq a z T hLists.1 hATy hZTy
      have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T := by
        rw [hCEqRec]
        exact hRecTy
      have hElimRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
            (__smtx_model_eval M (__eo_to_smt c)) :=
        smt_value_rel_str_nary_elim M hM c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hListRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) := by
        rw [hCEqRec]
        exact strConcat_smt_value_rel_list_concat_rec_eval M hM a z T
          hLists.1 hATy hZTy
      have hIntroTRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt t)) :=
        smt_value_rel_str_nary_intro M hM t T htTy
          (by simpa [a] using hIntroTNe)
      have hIntroEvalTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt (__seq_eval ts))) :=
        smt_value_rel_str_nary_intro M hM (__seq_eval ts) T
          hSeqEvalTsTy (by simpa [z] using hIntroEvalTsNe)
      have hZTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt ts)) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt z))
          (__smtx_model_eval M (__eo_to_smt (__seq_eval ts)))
          (__smtx_model_eval M (__eo_to_smt ts))
          hIntroEvalTsRel hSeqEvalTsRel
      have hConcatLeftRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z))) :=
        strConcat_smt_value_rel_left_congr M hM a t z T
          hATy htTy hZTy hIntroTRel
      have hConcatRightRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        strConcat_smt_value_rel_right_congr M hM t z ts T
          htTy hZTy htsTy hZTsRel
      have hConcatRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hListRel
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
            hConcatLeftRel hConcatRightRel)
      constructor
      · change __smtx_typeof (__eo_to_smt (__str_nary_elim c)) =
          __smtx_typeof (__eo_to_smt (mkConcat t ts))
        rw [smt_typeof_str_nary_elim_of_seq_ne_stuck c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)]
        exact (smt_typeof_str_concat_of_seq t ts T htTy htsTy).symm
      · change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hElimRel hConcatRel
  | case5 t n m =>
      sorry
  | case6 t s =>
      sorry
  | case7 t s r =>
      sorry
  | case8 t s r =>
      sorry
  | case9 t s n =>
      sorry
  | case10 t s =>
      sorry
  | case11 t s =>
      sorry
  | case12 t n =>
      sorry
  | case13 t =>
      sorry
  | case14 t _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      constructor
      · simp [__seq_eval]
      · simpa [__seq_eval] using
          RuleProofs.smt_value_rel_refl
            (__smtx_model_eval M (__eo_to_smt t))

private theorem seq_eval_smt_value_rel
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hEvalNe : __seq_eval t ≠ Term.Stuck)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
      (__smtx_model_eval M (__eo_to_smt t)) :=
  (seq_eval_smt_type_and_value_rel M hM t hEvalNe hNN).2

theorem cmd_step_seq_eval_op_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_eval_op args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_eval_op args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_eval_op args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
              change __eo_typeof (__eo_prog_seq_eval_op a1) = Term.Bool at hResultTy
              change __eo_prog_seq_eval_op a1 ≠ Term.Stuck at hProg
              cases a1 with
              | Apply f u =>
                  cases f with
                  | Apply eqop t =>
                      cases eqop with
                      | UOp op =>
                          cases op with
                          | eq =>
                              obtain ⟨hReqEq, hProgEq⟩ := seq_eval_op_shape hProg
                              have hArgTrans :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) := by
                                simpa [RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans.1
                              have hBodyTy :
                                  __eo_typeof
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
                                    Term.Bool := by
                                rw [← hProgEq]
                                exact hResultTy
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type _
                                  hArgTrans hBodyTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                  true
                                rw [hProgEq]
                                subst u
                                exact RuleProofs.eo_interprets_eq_of_rel M t
                                  (__seq_eval t) hEqBool <| by
                                    exact RuleProofs.smt_value_rel_symm
                                      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
                                      (__smtx_model_eval M (__eo_to_smt t))
                                      (seq_eval_smt_value_rel M hM t
                                        (by
                                          intro hStuck
                                          rw [hStuck] at hEqBool
                                          rcases
                                            RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                              t Term.Stuck hEqBool with
                                            ⟨hSame, hNN⟩
                                          have hStuckTy :
                                              __smtx_typeof (__eo_to_smt Term.Stuck) =
                                                SmtType.None := by
                                            change __smtx_typeof SmtTerm.None = SmtType.None
                                            exact TranslationProofs.smtx_typeof_none
                                          rw [hStuckTy] at hSame
                                          exact hNN hSame)
                                        ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                          t (__seq_eval t) hEqBool).2))
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hEqBool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
