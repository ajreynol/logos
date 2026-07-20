module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.SmtModel

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eq_has_bool_type_of_translation
    (x y : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  unfold RuleProofs.eo_has_bool_type
  have hNN :
      term_has_non_none_type
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  exact Smtm.eq_term_typeof_of_non_none hNN

theorem seq_eval_of_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    ∃ ss : SmtSeq,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss ∧
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char ∧
      native_string_valid (native_unpack_string ss) = true := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  rcases seq_value_canonical hPres with ⟨ss, hss⟩
  have hSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss] using hPres
  exact ⟨ss, hss, hSeqTy, native_unpack_string_valid_of_typeof_seq_char hSeqTy⟩

theorem reglan_eval_of_type
    (M : SmtModel) (hM : model_total_typed M) (r : Term)
    (hTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    ∃ rv : native_RegLan,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact reglan_value_canonical hPres

private theorem native_re_prefix_match_go_isSome_iff_exists
    (r : native_RegLan) :
  ∀ (xs : native_String) (n : Nat),
      native_string_valid xs = true ->
      ((Smtm.native_re_prefix_match_len?.go r xs n).isSome = true ↔
        ∃ pre : native_String, (∃ post : native_String,
          (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true))) := by
  intro xs n
  induction xs generalizing r n with
  | nil =>
      refine (fun hValid : native_string_valid [] = true => ?_)
      rw [Smtm.native_re_prefix_match_len?.go.eq_1]
      cases hNull : native_re_nullable r
      · simp [hNull, RuleProofs.nativeListInRe]
      · simp [hNull, RuleProofs.nativeListInRe]
  | cons c cs ih =>
      refine (fun hValid : native_string_valid (c :: cs) = true => ?_)
      have hParts : native_char_valid c = true ∧ native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      rcases hParts with ⟨hc, hcs⟩
      rw [Smtm.native_re_prefix_match_len?.go.eq_2]
      cases hNull : native_re_nullable r
      · simp [hc]
        constructor
        · intro h
          rcases (ih (native_re_deriv c r) (n + 1) hcs).1 h with
            ⟨pre, post, hAppend, hIn⟩
          refine Exists.intro (c :: pre) ?_
          constructor
          · exact ⟨post, by simp [hAppend]⟩
          · simpa [RuleProofs.nativeListInRe] using hIn
        · intro h
          rcases h with ⟨pre, hPost, hIn⟩
          cases pre with
          | nil =>
              have hNullable : native_re_nullable r = true := by
                simpa [RuleProofs.nativeListInRe] using hIn
              simp [hNull] at hNullable
          | cons d ds =>
              rcases hPost with ⟨post, hAppend⟩
              cases hAppend
              have hTailIn :
                  RuleProofs.nativeListInRe ds (native_re_deriv c r) = true := by
                simpa [RuleProofs.nativeListInRe] using hIn
              exact (ih (native_re_deriv c r) (n + 1) hcs).2
                ⟨ds, post, by rfl, hTailIn⟩
      · simp
        refine Exists.intro [] ?_
        constructor
        · exact ⟨c :: cs, by simp⟩
        · simpa [RuleProofs.nativeListInRe] using hNull

private theorem native_re_prefix_match_isSome_iff_exists
    (r : native_RegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    (native_re_prefix_match_len? r xs).isSome = true ↔
      ∃ pre : native_String, (∃ post : native_String,
        (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true)) := by
  rw [Smtm.native_re_prefix_match_len?.eq_1]
  have h := native_re_prefix_match_go_isSome_iff_exists r xs 0
  exact h hValid

private theorem nativeListInRe_concat_all_true_iff_exists
    (r : native_RegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) = true ↔
      ∃ pre : native_String, (∃ post : native_String,
        (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true)) := by
  constructor
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs r native_re_all).1
        (by simpa [native_re_concat] using h) with
      ⟨pre, post, hAppend, hLeft, _hRight⟩
    exact ⟨pre, post, hAppend, hLeft⟩
  · intro h
    rcases h with ⟨pre, post, hAppend, hLeft⟩
    have hAppendValid : native_string_valid (pre ++ post) = true := by
      simpa [hAppend] using hValid
    have hRight : RuleProofs.nativeListInRe post native_re_all = true := by
      have hAll : post.all native_char_valid = true := by
        have hAllAppend : (pre ++ post).all native_char_valid = true := by
          simpa [native_string_valid] using hAppendValid
        have hAllParts :
            pre.all native_char_valid = true ∧ post.all native_char_valid = true := by
          simpa [List.all_append, Bool.and_eq_true] using hAllAppend
        exact hAllParts.2
      exact RuleProofs.nativeListInRe_re_all post hAll
    simpa [native_re_concat] using
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs r native_re_all).2
        ⟨pre, post, hAppend, hLeft, hRight⟩

private theorem native_re_prefix_match_isSome_iff_concat_all
    (r : native_RegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    (native_re_prefix_match_len? r xs).isSome = true ↔
      RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) = true := by
  rw [native_re_prefix_match_isSome_iff_exists r xs hValid,
    nativeListInRe_concat_all_true_iff_exists r xs hValid]

private theorem native_str_in_re_concat_all_eq_prefix_isSome
    (r : native_RegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    native_str_in_re xs (native_re_concat r native_re_all) =
      (native_re_prefix_match_len? r xs).isSome := by
  have hIff := native_re_prefix_match_isSome_iff_concat_all r xs hValid
  have hNative :
      native_str_in_re xs (native_re_concat r native_re_all) =
        RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) := by
    simp [native_str_in_re, hValid, RuleProofs.nativeListInRe]
  rw [hNative]
  cases hPref : (native_re_prefix_match_len? r xs).isSome <;>
    cases hIn : RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) <;>
      simp [hPref, hIn] at hIff ⊢

def replace_re_search_re (r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
    (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))

theorem replace_re_search_re_eval
    (M : SmtModel) (r : Term) (rv : native_RegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_typeof (__eo_to_smt (replace_re_search_re r)) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt (replace_re_search_re r)) =
        SmtValue.RegLan (native_re_concat rv native_re_all) := by
  constructor
  · change __smtx_typeof
        (SmtTerm.re_concat (__eo_to_smt r)
          (SmtTerm.re_concat SmtTerm.re_all
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtType.RegLan
    simp [__smtx_typeof, hRTy, native_ite,
      native_Teq, native_string_valid]
  · change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt r)
          (SmtTerm.re_concat SmtTerm.re_all
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtValue.RegLan (native_re_concat rv native_re_all)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hREval,
      RuleProofs.native_unpack_string_pack_string, native_re_concat,
      native_re_all, native_re_mk_concat]
    cases rv <;> simp [native_str_to_re,
      native_re_of_list]

theorem str_first_match_rec_smallest_eq_go
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ (xs : native_String) (r : Term) (rv : native_RegLan) (n : Nat),
      native_string_valid xs = true ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __str_first_match_rec_smallest (substrWord xs 0 xs.length) r
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __str_first_match_rec_smallest (substrWord xs 0 xs.length) r
          (Term.Numeral (Int.ofNat n)) =
        match Smtm.native_re_prefix_match_len?.go rv xs n with
        | some endIdx => Term.Numeral (Int.ofNat endIdx)
        | none => Term.Stuck
  | [], r, rv, n, hValid, hRTy, hREval, hNe => by
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hStep :
          __str_first_match_rec_smallest
              (substrWord ([] : native_String) 0 ([] : native_String).length) r
              (Term.Numeral (Int.ofNat n)) =
            __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) := by
        change
          __str_first_match_rec_smallest (Term.String []) r
              (Term.Numeral (Int.ofNat n)) =
            __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n))
        exact
          Eo.__str_first_match_rec_smallest.eq_4 r
            (Term.Numeral (Int.ofNat n)) hRNe (by simp)
      have hNeReq :
          __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck := by
        intro hReqStuck
        exact hNe (hStep.trans hReqStuck)
      have hReq :
          __re_nullable r = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck (__re_nullable r) (Term.Boolean true)
          (Term.Numeral (Int.ofNat n)) hNeReq
      have hNullNe : __re_nullable r ≠ Term.Stuck :=
        eo_requires_left_ne_stuck_of_ne_stuck (__re_nullable r)
          (Term.Boolean true) (Term.Numeral (Int.ofNat n)) hNeReq
      have hReqResult :
          __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) =
            Term.Numeral (Int.ofNat n) :=
        eo_requires_result_eq_of_ne_stuck (__re_nullable r)
          (Term.Boolean true) (Term.Numeral (Int.ofNat n)) hNeReq
      have hNullEq :
          __re_nullable r = Term.Boolean (native_re_nullable rv) := by
        have h :=
          str_eval_str_in_re_rec_substrWord_eq M hM [] r rv
            (by simp [native_string_valid]) hRTy hREval (by
              simpa [substrWord, str_eval_empty_eq_nullable] using hNullNe)
        simpa [substrWord, str_eval_empty_eq_nullable, native_str_in_re,
          hValid] using h
      cases hNull : native_re_nullable rv
      · have hFalse : False := by
          rw [hNull] at hNullEq
          rw [hReq] at hNullEq
          cases hNullEq
        exact False.elim hFalse
      · rw [Smtm.native_re_prefix_match_len?.go.eq_1]
        simp [hNull]
        exact hStep.trans hReqResult
  | c :: cs, r, rv, n, hValid, hRTy, hREval, hNe => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hAdd :
          __eo_add (Term.Numeral (Int.ofNat n)) (Term.Numeral 1) =
            Term.Numeral (Int.ofNat (n + 1)) := by
        simp [__eo_add, native_zplus]
      have hStep :
          __str_first_match_rec_smallest
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) r (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__re_nullable r) (Term.Numeral (Int.ofNat n))
              (__str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1)))) := by
        rw [Eo.__str_first_match_rec_smallest.eq_3 r
          (Term.Numeral (Int.ofNat n)) (Term.String [c])
          (substrWord cs 0 cs.length) hRNe (by simp)]
        rw [hAdd]
      have hNeIte :
          __eo_ite (__re_nullable r) (Term.Numeral (Int.ofNat n))
              (__str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1)))) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      refine hStep.trans ?_
      have hNullNe : __re_nullable r ≠ Term.Stuck := by
        intro hNullStuck
        rw [hNullStuck] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hNullEq :
          __re_nullable r = Term.Boolean (native_re_nullable rv) := by
        have h :=
          str_eval_str_in_re_rec_substrWord_eq M hM [] r rv
            (by simp [native_string_valid]) hRTy hREval (by
              simpa [substrWord, str_eval_empty_eq_nullable] using hNullNe)
        simpa [substrWord, str_eval_empty_eq_nullable, native_str_in_re] using h
      cases hNull : native_re_nullable rv
      · rw [hNull] at hNullEq
        rw [hNullEq] at hNeIte ⊢
        simp [__eo_ite, native_teq, native_ite] at hNeIte ⊢
        have hDerNe : __derivative (Term.String [c]) r ≠ Term.Stuck := by
          intro hDer
          rw [hDer] at hNeIte
          have hStuck :
              __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                  Term.Stuck (Term.Numeral (Int.ofNat n + 1)) =
                Term.Stuck :=
            Eo.__str_first_match_rec_smallest.eq_1
              (substrWord cs 0 cs.length) (Term.Numeral (Int.ofNat n + 1))
          exact hNeIte hStuck
        rcases
          smtx_model_eval_derivative_single_rel M hM c hc r rv hRTy hREval
            hDerNe with
          ⟨drv, hDerEval, hDerTy, hDerRel⟩
        have hNeTail :
            __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1))) ≠ Term.Stuck := by
          simpa using hNeIte
        have hTail :=
          str_first_match_rec_smallest_eq_go M hM cs
            (__derivative (Term.String [c]) r) drv (n + 1)
            hcs hDerTy hDerEval hNeTail
        have hTail' :
            __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat n + 1)) =
              match Smtm.native_re_prefix_match_len?.go drv cs (n + 1) with
              | some endIdx => Term.Numeral (Int.ofNat endIdx)
              | none => Term.Stuck := by
          simpa using hTail
        change
          __str_first_match_rec_smallest (substrWord cs 0 cs.length)
              (__derivative (Term.String [c]) r)
              (Term.Numeral (Int.ofNat n + 1)) =
            match Smtm.native_re_prefix_match_len?.go rv (c :: cs) n with
            | some endIdx => Term.Numeral (Int.ofNat endIdx)
            | none => Term.Stuck
        rw [hTail']
        have hGoCong :
            Smtm.native_re_prefix_match_len?.go drv cs (n + 1) =
              Smtm.native_re_prefix_match_len?.go
                (native_re_deriv c rv) cs (n + 1) :=
          CongSupport.native_re_prefix_match_len_go_congr_valid_ext_of_str_ext cs drv
            (native_re_deriv c rv) (n + 1) (by
              intro ys hys
              exact smt_value_rel_reglan_valid_eq hDerRel hys)
        rw [Smtm.native_re_prefix_match_len?.go.eq_2]
        simp [hNull, hc]
        rw [← hGoCong]
      · rw [hNull] at hNullEq
        rw [hNullEq]
        rw [Smtm.native_re_prefix_match_len?.go.eq_2]
        simp [__eo_ite, native_teq, native_ite, hNull]

theorem str_eval_prefix_condition_eq
    (M : SmtModel) (hM : model_total_typed M)
    (xs : native_String) (rs : Term) (rv : native_RegLan)
    (hValid : native_string_valid xs = true)
    (hRsTy : __smtx_typeof (__eo_to_smt rs) = SmtType.RegLan)
    (hRsEval :
      __smtx_model_eval M (__eo_to_smt rs) =
        SmtValue.RegLan (native_re_concat rv native_re_all))
    (hCondNe :
      __str_eval_str_in_re_rec (substrWord xs 0 xs.length) rs ≠ Term.Stuck) :
    __str_eval_str_in_re_rec (substrWord xs 0 xs.length) rs =
      Term.Boolean ((native_re_prefix_match_len? rv xs).isSome) := by
  have hEval :=
    str_eval_str_in_re_rec_substrWord_eq M hM xs rs
      (native_re_concat rv native_re_all) hValid hRsTy hRsEval hCondNe
  rw [hEval]
  rw [native_str_in_re_concat_all_eq_prefix_isSome rv xs hValid]

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

theorem native_pack_seq_char_append_unpack_string
    (pre suf : native_String) (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_seq SmtType.Char
        (pre.map SmtValue.Char ++ native_unpack_seq ss ++ suf.map SmtValue.Char) =
      native_pack_string (pre ++ native_unpack_string ss ++ suf) := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hMap' :
      List.map SmtValue.Char
          (List.map native_ssm_char_of_value (native_unpack_seq ss)) =
        native_unpack_seq ss := by
    simpa [List.map_map] using hMap
  unfold native_pack_string native_unpack_string
  simp only [List.map_append]
  rw [hMap']

private def replace_re_match_pair (idx endIdx : Nat) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_pair)
      (Term.Numeral (Int.ofNat idx)))
    (Term.Numeral (Int.ofNat endIdx))

private def replace_re_no_match_pair : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_pair)
      (Term.Numeral (-1 : native_Int)))
    (Term.Numeral (-1 : native_Int))

private theorem str_first_match_rec_eq_find_aux
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ (xs : native_String) (r rs : Term) (rv : native_RegLan) (n : Nat),
      native_string_valid xs = true ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_typeof (__eo_to_smt rs) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt rs) =
        SmtValue.RegLan (native_re_concat rv native_re_all) ->
      __str_first_match_rec (substrWord xs 0 xs.length) r rs
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __str_first_match_rec (substrWord xs 0 xs.length) r rs
          (Term.Numeral (Int.ofNat n)) =
        match native_re_find_idx_aux rv xs n with
        | some (idx, len) => replace_re_match_pair idx (idx + len)
        | none => replace_re_no_match_pair
  | [], r, rs, rv, n, hValid, hRTy, hREval, hRsTy, hRsEval, hNe => by
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hRsNe : rs ≠ Term.Stuck := by
        intro hRs
        subst rs
        change __smtx_model_eval M SmtTerm.None =
          SmtValue.RegLan (native_re_concat rv native_re_all) at hRsEval
        simp [__smtx_model_eval] at hRsEval
      have hStep :
          __str_first_match_rec
              (substrWord ([] : native_String) 0 ([] : native_String).length) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair := by
        change
          __str_first_match_rec (Term.String []) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair
        simpa [replace_re_no_match_pair] using
          Eo.__str_first_match_rec.eq_5 r rs
            (Term.Numeral (Int.ofNat n)) hRNe hRsNe (by simp)
      have hNeIte :
          __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      have hCondNe : __str_eval_str_in_re_rec (Term.String []) rs ≠ Term.Stuck := by
        intro hCond
        rw [hCond] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hCondEq :
          __str_eval_str_in_re_rec (Term.String []) rs =
            Term.Boolean ((native_re_prefix_match_len? rv ([] : native_String)).isSome) := by
        simpa [substrWord] using
          str_eval_prefix_condition_eq M hM [] rs rv
            (by simp [native_string_valid]) hRsTy hRsEval
            (by simpa [substrWord] using hCondNe)
      cases hPref : native_re_prefix_match_len? rv ([] : native_String) with
      | none =>
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.native_re_find_idx_aux.eq_1]
          simp [hPref, __eo_ite, native_teq, native_ite]
      | some len =>
          have hBranchNe :
              __eo_mk_apply
                  ((Term.UOp UserOp._at__at_pair).Apply
                    (Term.Numeral (Int.ofNat n)))
                  (__eo_add (Term.Numeral (Int.ofNat n))
                    (__str_first_match_rec_smallest (Term.String []) r
                      (Term.Numeral 0))) ≠ Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hSmallNe :
              __str_first_match_rec_smallest (Term.String []) r
                  (Term.Numeral 0) ≠ Term.Stuck := by
            intro hSmall
            rw [hSmall] at hBranchNe
            simp [__eo_add, __eo_mk_apply] at hBranchNe
          have hSmall :=
            str_first_match_rec_smallest_eq_go M hM [] r rv 0
              (by simp [native_string_valid]) hRTy hREval
              (by simpa [substrWord] using hSmallNe)
          have hGoPref :
              Smtm.native_re_prefix_match_len?.go rv ([] : native_String) 0 =
                some len := by
            simpa [Smtm.native_re_prefix_match_len?.eq_1] using hPref
          have hSmall' :
              __str_first_match_rec_smallest (Term.String []) r
                  (Term.Numeral 0) =
                match Smtm.native_re_prefix_match_len?.go rv ([] : native_String) 0 with
                | some endIdx => Term.Numeral (Int.ofNat endIdx)
                | none => Term.Stuck := by
            simpa [substrWord] using hSmall
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.native_re_find_idx_aux.eq_1]
          simp [hPref, __eo_ite, native_teq, native_ite]
          rw [hSmall', hGoPref]
          simp [replace_re_match_pair, __eo_add, native_zplus, __eo_mk_apply]
  | c :: cs, r, rs, rv, n, hValid, hRTy, hREval, hRsTy, hRsEval, hNe => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hRsNe : rs ≠ Term.Stuck := by
        intro hRs
        subst rs
        change __smtx_model_eval M SmtTerm.None =
          SmtValue.RegLan (native_re_concat rv native_re_all) at hRsEval
        simp [__smtx_model_eval] at hRsEval
      have hAdd :
          __eo_add (Term.Numeral (Int.ofNat n)) (Term.Numeral 1) =
            Term.Numeral (Int.ofNat (n + 1)) := by
        simp [__eo_add, native_zplus]
      have hStep :
          __str_first_match_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite
              (__str_eval_str_in_re_rec
                (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                  (substrWord cs 0 cs.length)) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest
                    (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                      (substrWord cs 0 cs.length)) r (Term.Numeral 0))))
              (__str_first_match_rec (substrWord cs 0 cs.length) r rs
                (Term.Numeral (Int.ofNat (n + 1)))) := by
        rw [Eo.__str_first_match_rec.eq_4 r rs
          (Term.Numeral (Int.ofNat n)) (Term.String [c])
          (substrWord cs 0 cs.length) hRNe hRsNe (by simp)]
        rw [hAdd]
      have hNeIte :
          __eo_ite
              (__str_eval_str_in_re_rec
                (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                  (substrWord cs 0 cs.length)) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest
                    (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                      (substrWord cs 0 cs.length)) r (Term.Numeral 0))))
              (__str_first_match_rec (substrWord cs 0 cs.length) r rs
                (Term.Numeral (Int.ofNat (n + 1)))) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      have hCondNe :
          __str_eval_str_in_re_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) rs ≠ Term.Stuck := by
        intro hCond
        rw [hCond] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hCondEq :
          __str_eval_str_in_re_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) rs =
            Term.Boolean ((native_re_prefix_match_len? rv (c :: cs)).isSome) := by
        have h :=
          str_eval_prefix_condition_eq M hM (c :: cs) rs rv
            hValid hRsTy hRsEval (by
              simpa [substrWord, extractString_zero_cons,
                substrWord_cons_tail] using hCondNe)
        simpa [substrWord, extractString_zero_cons,
          substrWord_cons_tail] using h
      cases hPref : native_re_prefix_match_len? rv (c :: cs) with
      | some len =>
          have hBranchNe :
              __eo_mk_apply
                  ((Term.UOp UserOp._at__at_pair).Apply
                    (Term.Numeral (Int.ofNat n)))
                  (__eo_add (Term.Numeral (Int.ofNat n))
                    (__str_first_match_rec_smallest
                      (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                        (substrWord cs 0 cs.length)) r (Term.Numeral 0))) ≠
                Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hSmallNe :
              __str_first_match_rec_smallest
                  (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                    (substrWord cs 0 cs.length)) r (Term.Numeral 0) ≠
                Term.Stuck := by
            intro hSmall
            rw [hSmall] at hBranchNe
            simp [__eo_add, __eo_mk_apply] at hBranchNe
          have hSmall :=
            str_first_match_rec_smallest_eq_go M hM (c :: cs) r rv 0
              hValid hRTy hREval (by
                simpa [substrWord, extractString_zero_cons,
                  substrWord_cons_tail] using hSmallNe)
          have hGoPref :
              Smtm.native_re_prefix_match_len?.go rv (c :: cs) 0 =
                some len := by
            simpa [Smtm.native_re_prefix_match_len?.eq_1] using hPref
          have hSmall' :
              __str_first_match_rec_smallest
                  (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                    (substrWord cs 0 cs.length)) r (Term.Numeral 0) =
                match Smtm.native_re_prefix_match_len?.go rv (c :: cs) 0 with
                | some endIdx => Term.Numeral (Int.ofNat endIdx)
                | none => Term.Stuck := by
            simpa [substrWord, extractString_zero_cons,
              substrWord_cons_tail] using hSmall
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.native_re_find_idx_aux.eq_2]
          simp [hPref, __eo_ite, native_teq, native_ite]
          rw [hSmall', hGoPref]
          simp [replace_re_match_pair, __eo_add, native_zplus, __eo_mk_apply]
      | none =>
          have hTailNe :
              __str_first_match_rec (substrWord cs 0 cs.length) r rs
                  (Term.Numeral (Int.ofNat (n + 1))) ≠ Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hTail :=
            str_first_match_rec_eq_find_aux M hM cs r rs rv (n + 1)
              hcs hRTy hREval hRsTy hRsEval hTailNe
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.native_re_find_idx_aux.eq_2]
          simp [hPref, __eo_ite, native_teq, native_ite]
          exact hTail

end RuleProofs
