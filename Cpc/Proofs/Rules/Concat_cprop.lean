import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatCPropNormalize (rev x : Term) : Term :=
  concatSplitNormalize rev x

private abbrev concatCPropHead (rev x : Term) : Term :=
  concatSplitHead rev x

private abbrev concatCPropSecond (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatCPropNormalize rev x)
    (Term.Numeral 1)

private abbrev concatCPropFlatSecond (rev x : Term) : Term :=
  __str_flatten (__str_nary_intro (concatCPropSecond rev x))

private abbrev concatCPropSHeadTailWord (rev s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let sHeadLen := __eo_len sHead
  __str_flatten
    (__str_nary_intro
      (__eo_ite rev
        (__eo_extract sHead (Term.Numeral 0)
          (__eo_add sHeadLen (Term.Numeral (-2 : native_Int))))
        (__eo_extract sHead (Term.Numeral 1) sHeadLen)))

private abbrev concatCPropOverlapLen (rev t s : Term) : Term :=
  __eo_add (Term.Numeral 1)
    (__str_overlap_rec
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropSHeadTailWord rev s))
        (concatCPropSHeadTailWord rev s))
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropFlatSecond rev t))
        (concatCPropFlatSecond rev t)))

private abbrev concatCPropPrefix (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  __eo_mk_apply
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (Term.Numeral 0))
    (concatCPropOverlapLen rev t s)

private abbrev concatCPropSuffix (rev t s tc : Term) : Term :=
  let pfx := concatCPropPrefix rev t s
  Term.UOp1 UserOp1._at_purify
    (__eo_mk_apply
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)))

private abbrev concatCPropReverseSuffix (rev t s tc : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  let endPart :=
    __eo_mk_apply
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
          k))
      k
  Term.UOp1 UserOp1._at_purify
    (__eo_mk_apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)))

private abbrev concatCPropReverseEnd (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.neg)
          (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
        k))
    k

private abbrev concatCPropFormula (rev t s tc : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
    (__eo_ite rev
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropReverseSuffix rev t s tc))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropReverseEnd rev t s))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropReverseSuffix rev t s tc)))))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropPrefix rev t s))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropSuffix rev t s tc))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropPrefix rev t s))))))

private abbrev concatCPropBody (rev t s tc : Term) : Term :=
  __eo_requires (concatCPropHead rev t) tc (concatCPropFormula rev t s tc)

private theorem len_nonzero_seq_type_of_bool (u : Term)
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) :
    ∃ T, __smtx_typeof (__eo_to_smt u) = SmtType.Seq T := by
  have hEqBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen u) (Term.Numeral 0)) :=
    RuleProofs.eo_has_bool_type_not_arg
      (mkEq (mkStrLen u) (Term.Numeral 0)) hNonzeroBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen u) (Term.Numeral 0) hEqBool with
    ⟨_hSame, hLeftNN⟩
  have hLenTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt u)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen] using hLeftNN
  exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
    (typeof_str_len_eq (__eo_to_smt u)) hLenTerm

private theorem cprop_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem cprop_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem cprop_mk_apply_eq_apply_of_args_ne_stuck (f x : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem cprop_seq_type_ne_stuck (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    x ≠ Term.Stuck :=
  RuleProofs.term_ne_stuck_of_has_smt_translation x
    (by unfold RuleProofs.eo_has_smt_translation; rw [hxTy]; exact seq_ne_none T)

private theorem smt_typeof_eo_add_one_of_ne_stuck (x : Term)
    (h : __eo_add (Term.Numeral 1) x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_add (Term.Numeral 1) x)) =
      SmtType.Int := by
  cases x <;> simp [__eo_add] at h ⊢
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral (native_zplus 1 n)) = SmtType.Int
    rw [__smtx_typeof.eq_2]

private theorem cprop_eo_add_one_arg_ne_stuck (x : Term)
    (h : __eo_add (Term.Numeral 1) x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  cases x <;> simp [__eo_add] at h ⊢

private theorem str_overlap_rec_numeral_of_ne_stuck :
    ∀ (a b : Term), __str_overlap_rec a b ≠ Term.Stuck →
      ∃ n : Nat, __str_overlap_rec a b = Term.Numeral (Int.ofNat n) := by
  intro a b h
  cases a with
  | Stuck =>
      simp [__str_overlap_rec] at h
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at h
                · have hDef :
                      __str_overlap_rec
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) y) x) b =
                        __eo_ite
                          (__str_is_compatible
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) y) x) b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [__str_overlap_rec] at hb ⊢
                  cases hCompat :
                      __str_is_compatible
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)
                        b with
                  | Boolean bv =>
                      cases bv
                      · have hRecNe : __str_overlap_rec x b ≠ Term.Stuck := by
                          apply cprop_eo_add_one_arg_ne_stuck
                          simpa [hDef, hCompat, __eo_ite, native_ite, native_teq] using h
                        rcases str_overlap_rec_numeral_of_ne_stuck x b hRecNe with
                          ⟨n, hRec⟩
                        refine ⟨n + 1, ?_⟩
                        rw [hDef, hCompat, hRec]
                        simp [__eo_ite, __eo_add, native_zplus, native_ite, native_teq]
                        rw [Int.add_comm]
                      · refine ⟨0, ?_⟩
                        rw [hDef, hCompat]
                        simp [__eo_ite, native_ite, native_teq]
                  | _ =>
                      simp [hDef, hCompat, __eo_ite, native_ite, native_teq] at h
              · cases b <;> simp [__str_overlap_rec, hOp] at h ⊢ <;>
                  try exact ⟨0, rfl⟩
          | _ =>
              cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
                try exact ⟨0, rfl⟩
      | _ =>
          cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
            try exact ⟨0, rfl⟩
  | _ =>
      cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
        try exact ⟨0, rfl⟩
termination_by a b _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private def strConcatDrop : Term → Nat → Term
  | a, 0 => a
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _) tail, n + 1 =>
      strConcatDrop tail n
  | a, _ + 1 => a

private theorem nat_zero_of_term_numeral_zero_eq (m : Nat)
    (h : Term.Numeral (0 : native_Int) = Term.Numeral (Int.ofNat m)) :
    m = 0 := by
  injection h with hInt
  exact Int.ofNat_eq_zero.mp hInt.symm

private theorem nat_succ_of_term_numeral_add_one_eq (m r : Nat)
    (h :
      Term.Numeral (native_zplus (1 : native_Int) (Int.ofNat r)) =
        Term.Numeral (Int.ofNat m)) :
    m = r + 1 := by
  injection h with hInt
  have hCast : Int.ofNat m = Int.ofNat (r + 1) := by
    rw [← hInt]
    simp [native_zplus]
    omega
  exact Int.ofNat_inj.mp hCast

private theorem str_overlap_rec_le_of_compatible_drop :
    ∀ (a b : Term) (m n : Nat),
      __str_overlap_rec a b = Term.Numeral (Int.ofNat m) →
      __str_is_compatible (strConcatDrop a n) b = Term.Boolean true →
      m <= n := by
  intro a b m n hRec hCompat
  cases a with
  | Stuck =>
      cases b <;> simp [__str_overlap_rec] at hRec
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at hRec
                · let aCons :=
                    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x
                  have hDef :
                      __str_overlap_rec aCons b =
                        __eo_ite (__str_is_compatible aCons b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [aCons, __str_overlap_rec] at hb ⊢
                  cases hComp : __str_is_compatible aCons b with
                  | Boolean bv =>
                      cases bv
                      · cases n with
                        | zero =>
                            simp [aCons, strConcatDrop, hComp] at hCompat
                        | succ n =>
                            have hRecArg :
                                __str_overlap_rec x b ≠ Term.Stuck := by
                              have hAddEq :
                                  __eo_add (Term.Numeral 1)
                                      (__str_overlap_rec x b) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp] at hRec
                                simpa [__eo_ite, native_ite, native_teq]
                                  using hRec
                              intro hStuck
                              rw [hStuck] at hAddEq
                              simp [__eo_add] at hAddEq
                            rcases str_overlap_rec_numeral_of_ne_stuck x b
                                hRecArg with
                              ⟨r, hTailRec⟩
                            have hm : m = r + 1 := by
                              have hTerm :
                                  Term.Numeral
                                      (native_zplus (1 : native_Int)
                                        (Int.ofNat r)) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp, hTailRec] at hRec
                                simpa [__eo_ite, __eo_add, native_ite,
                                  native_teq] using hRec
                              exact nat_succ_of_term_numeral_add_one_eq m r
                                hTerm
                            have hTailCompat :
                                __str_is_compatible (strConcatDrop x n) b =
                                  Term.Boolean true := by
                              simpa [aCons, strConcatDrop] using hCompat
                            have hrle :
                                r <= n :=
                              str_overlap_rec_le_of_compatible_drop x b r n
                                hTailRec hTailCompat
                            omega
                      · rw [hDef, hComp] at hRec
                        have hm0 : m = 0 :=
                          nat_zero_of_term_numeral_zero_eq m
                            (by
                              simpa [__eo_ite, native_ite, native_teq]
                                using hRec)
                        omega
                  | _ =>
                      rw [hDef, hComp] at hRec
                      simp [__eo_ite, native_ite, native_teq] at hRec
              · cases b <;>
                  simp [__str_overlap_rec, hOp] at hRec <;>
                  (have hm0 : m = 0 :=
                    nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                   omega)
          | _ =>
              cases b <;> simp [__str_overlap_rec] at hRec <;>
                (have hm0 : m = 0 :=
                  nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                 omega)
      | _ =>
          cases b <;> simp [__str_overlap_rec] at hRec <;>
            (have hm0 : m = 0 :=
              nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
             omega)
  | _ =>
      cases b <;> simp [__str_overlap_rec] at hRec <;>
        (have hm0 : m = 0 :=
          nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
         omega)
termination_by a b m n _ _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private theorem str_overlap_rec_compatible_drop_false_of_lt :
    ∀ (a b : Term) (m n : Nat),
      __str_overlap_rec a b = Term.Numeral (Int.ofNat m) →
      n < m →
      __str_is_compatible (strConcatDrop a n) b = Term.Boolean false := by
  intro a b m n hRec hLt
  cases a with
  | Stuck =>
      cases b <;> simp [__str_overlap_rec] at hRec
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at hRec
                · let aCons :=
                    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x
                  have hDef :
                      __str_overlap_rec aCons b =
                        __eo_ite (__str_is_compatible aCons b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [aCons, __str_overlap_rec] at hb ⊢
                  cases hComp : __str_is_compatible aCons b with
                  | Boolean bv =>
                      cases bv
                      · cases n with
                        | zero =>
                            simpa [aCons, strConcatDrop] using hComp
                        | succ n =>
                            have hRecArg :
                                __str_overlap_rec x b ≠ Term.Stuck := by
                              have hAddEq :
                                  __eo_add (Term.Numeral 1)
                                      (__str_overlap_rec x b) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp] at hRec
                                simpa [__eo_ite, native_ite, native_teq]
                                  using hRec
                              intro hStuck
                              rw [hStuck] at hAddEq
                              simp [__eo_add] at hAddEq
                            rcases str_overlap_rec_numeral_of_ne_stuck x b
                                hRecArg with
                              ⟨r, hTailRec⟩
                            have hm : m = r + 1 := by
                              have hTerm :
                                  Term.Numeral
                                      (native_zplus (1 : native_Int)
                                        (Int.ofNat r)) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp, hTailRec] at hRec
                                simpa [__eo_ite, __eo_add, native_ite,
                                  native_teq] using hRec
                              exact nat_succ_of_term_numeral_add_one_eq m r
                                hTerm
                            have hnLt : n < r := by omega
                            have hTailFalse :
                                __str_is_compatible (strConcatDrop x n) b =
                                  Term.Boolean false :=
                              str_overlap_rec_compatible_drop_false_of_lt
                                x b r n hTailRec hnLt
                            simpa [aCons, strConcatDrop] using hTailFalse
                      · rw [hDef, hComp] at hRec
                        have hm0 : m = 0 :=
                          nat_zero_of_term_numeral_zero_eq m
                            (by
                              simpa [__eo_ite, native_ite, native_teq]
                                using hRec)
                        omega
                  | _ =>
                      rw [hDef, hComp] at hRec
                      simp [__eo_ite, native_ite, native_teq] at hRec
              · cases b <;>
                  simp [__str_overlap_rec, hOp] at hRec <;>
                  (have hm0 : m = 0 :=
                    nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                   omega)
          | _ =>
              cases b <;> simp [__str_overlap_rec] at hRec <;>
                (have hm0 : m = 0 :=
                  nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                 omega)
      | _ =>
          cases b <;> simp [__str_overlap_rec] at hRec <;>
            (have hm0 : m = 0 :=
              nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
             omega)
  | _ =>
      cases b <;> simp [__str_overlap_rec] at hRec <;>
        (have hm0 : m = 0 :=
          nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
         omega)
termination_by a b m n _ _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private theorem eo_list_nth_one_str_concat_cons_eq_tail_zero
    (head tail : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true) :
    __eo_list_nth (Term.UOp UserOp.str_concat) (mkConcat head tail)
        (Term.Numeral 1) =
      __eo_list_nth (Term.UOp UserOp.str_concat) tail (Term.Numeral 0) := by
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true := by
    simpa [mkConcat] using
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) head tail (by simp)
      hTailList
  simp [__eo_list_nth, __eo_list_nth_rec, mkConcat, hConsList,
    hTailList, __eo_add, native_zplus]

private theorem str_overlap_rec_left_ne_stuck_of_ne_stuck
    (a b : Term) (h : __str_overlap_rec a b ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  cases b <;> simp [__str_overlap_rec] at h

private theorem str_overlap_rec_right_ne_stuck_of_ne_stuck
    (a b : Term) (h : __str_overlap_rec a b ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> simp [__str_overlap_rec] at h

private theorem cprop_false_head_string_of_tailword_ne
    (s sc : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean false) s ≠ Term.Stuck) :
    ∃ cs : native_String, sc = Term.String cs := by
  cases sc with
  | String cs =>
      exact ⟨cs, rfl⟩
  | Binary w n =>
      change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hscTy
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [__smtx_typeof, hCond, native_ite] at hscTy
  | _ =>
      have hBad :
          concatCPropSHeadTailWord (Term.Boolean false) s = Term.Stuck := by
        simp [concatCPropSHeadTailWord, eo_ite_false, __eo_len,
          __eo_extract, __str_nary_intro, __str_flatten, ← hScEq]
      exact False.elim (hTailWordNe hBad)

private theorem cprop_true_head_string_of_tailword_ne
    (s sc : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean true) s ≠ Term.Stuck) :
    ∃ cs : native_String, sc = Term.String cs := by
  cases sc with
  | String cs =>
      exact ⟨cs, rfl⟩
  | Binary w n =>
      change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hscTy
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [__smtx_typeof, hCond, native_ite] at hscTy
  | _ =>
      have hBad :
          concatCPropSHeadTailWord (Term.Boolean true) s = Term.Stuck := by
        simp [concatCPropSHeadTailWord, eo_ite_true, __eo_len,
          __eo_extract, __str_nary_intro, __str_flatten, ← hScEq]
      exact False.elim (hTailWordNe hBad)

private theorem strConcatDrop_substrWord
    (s : native_String) :
    ∀ (n d : Nat) (start : native_Int),
      d <= n ->
      strConcatDrop (RuleProofs.substrWord s start n) d =
        RuleProofs.substrWord s (start + Int.ofNat d) (n - d)
  | _n, 0, _start, _h => by
      simp [strConcatDrop]
  | 0, d + 1, _start, h => by
      omega
  | n + 1, d + 1, start, h => by
      simp [RuleProofs.substrWord, strConcatDrop]
      have hdn : d <= n := Nat.succ_le_succ_iff.mp h
      have hDrop :=
        strConcatDrop_substrWord s n d (start + 1) hdn
      rw [hDrop]
      have hStart :
          start + 1 + Int.ofNat d = start + (Int.ofNat d + 1) := by
        ac_rfl
      rw [hStart]
      simp

private theorem native_unpack_seq_pack_string (s : native_String) :
    native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char := by
  simp [native_pack_string, RuleProofs.native_unpack_seq_pack_seq]

private theorem string_eval_unpack_eq
    (M : SmtModel) (s : native_String) (ss : SmtSeq)
    (hEval :
      __smtx_model_eval M (__eo_to_smt (Term.String s)) =
        SmtValue.Seq ss) :
    native_unpack_seq ss = s.map SmtValue.Char := by
  change __smtx_model_eval M (SmtTerm.String s) = SmtValue.Seq ss at hEval
  rw [__smtx_model_eval.eq_4] at hEval
  injection hEval with hSeq
  rw [← hSeq]
  simp [native_pack_string, native_unpack_pack_seq]

private theorem mkConcat_eval_unpack_eq
    (M : SmtModel) (x y : Term) (sxy sx sy : SmtSeq)
    (hxyEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    native_unpack_seq sxy =
      native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hyEval] at hxyEval
  simp [__smtx_model_eval_str_concat, native_seq_concat] at hxyEval
  rw [← hxyEval]
  simp [native_unpack_pack_seq]

private theorem str_flatten_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_flatten x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_flatten] at h

private theorem cprop_flat_second_false_tail_head_of_ne_stuck
    (t tc tTail : Term)
    (hIntroT : __str_nary_intro t = mkConcat tc tTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hFlatNe : concatCPropFlatSecond (Term.Boolean false) t ≠ Term.Stuck) :
    ∃ x xTail,
      tTail = mkConcat x xTail ∧
        __eo_is_list (Term.UOp UserOp.str_concat) xTail = Term.Boolean true ∧
        concatCPropFlatSecond (Term.Boolean false) t =
          __str_flatten (__str_nary_intro x) := by
  have hSecondEq :
      concatCPropSecond (Term.Boolean false) t =
        __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) := by
    simpa [concatCPropSecond, concatCPropNormalize, concatSplitNormalize,
      eo_ite_false, hIntroT] using
      eo_list_nth_one_str_concat_cons_eq_tail_zero tc tTail hTTailList
  have hIntroSecondNe :
      __str_nary_intro (concatCPropSecond (Term.Boolean false) t) ≠
        Term.Stuck :=
    str_flatten_arg_ne_stuck_of_ne_stuck
      (__str_nary_intro (concatCPropSecond (Term.Boolean false) t))
      hFlatNe
  have hSecondNe :
      concatCPropSecond (Term.Boolean false) t ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (concatCPropSecond (Term.Boolean false) t) hIntroSecondNe
  have hNthNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) ≠ Term.Stuck := by
    rwa [hSecondEq] at hSecondNe
  let x :=
    __eo_list_nth (Term.UOp UserOp.str_concat) tTail (Term.Numeral 0)
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) tTail x rfl (by simpa [x] using hNthNe)
    with ⟨xTail, hTailEq, hXTailList⟩
  refine ⟨x, xTail, hTailEq, hXTailList, ?_⟩
  simp [concatCPropFlatSecond, hSecondEq, x]

private theorem cprop_flat_second_true_tail_head_of_rev_ne_stuck
    (t tc tTail : Term)
    (hRevIntroT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hRevFlatNe :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropFlatSecond (Term.Boolean true) t) ≠ Term.Stuck) :
    ∃ x xTail,
      tTail = mkConcat x xTail ∧
        __eo_is_list (Term.UOp UserOp.str_concat) xTail = Term.Boolean true ∧
        concatCPropFlatSecond (Term.Boolean true) t =
          __str_flatten (__str_nary_intro x) := by
  have hFlatNe : concatCPropFlatSecond (Term.Boolean true) t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (concatCPropFlatSecond (Term.Boolean true) t) hRevFlatNe
  have hSecondEq :
      concatCPropSecond (Term.Boolean true) t =
        __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) := by
    simpa [concatCPropSecond, concatCPropNormalize, concatSplitNormalize,
      eo_ite_true, hRevIntroT] using
      eo_list_nth_one_str_concat_cons_eq_tail_zero tc tTail hTTailList
  have hIntroSecondNe :
      __str_nary_intro (concatCPropSecond (Term.Boolean true) t) ≠
        Term.Stuck :=
    str_flatten_arg_ne_stuck_of_ne_stuck
      (__str_nary_intro (concatCPropSecond (Term.Boolean true) t))
      hFlatNe
  have hSecondNe :
      concatCPropSecond (Term.Boolean true) t ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (concatCPropSecond (Term.Boolean true) t) hIntroSecondNe
  have hNthNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) ≠ Term.Stuck := by
    rwa [hSecondEq] at hSecondNe
  let x :=
    __eo_list_nth (Term.UOp UserOp.str_concat) tTail (Term.Numeral 0)
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) tTail x rfl (by simpa [x] using hNthNe)
    with ⟨xTail, hTailEq, hXTailList⟩
  refine ⟨x, xTail, hTailEq, hXTailList, ?_⟩
  simp [concatCPropFlatSecond, hSecondEq, x]

private theorem eo_prog_concat_cprop_eq_of_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
      concatCPropFormula rev t s tc ∧
      concatCPropHead rev t = tc := by
  have hProgBody :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
        concatCPropBody rev t s tc := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals rfl
  have hBodyNe : concatCPropBody rev t s tc ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadT : concatCPropHead rev t = tc :=
    eo_requires_eq_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  have hFormulaEq :
      concatCPropBody rev t s tc = concatCPropFormula rev t s tc :=
    eo_requires_eq_result_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  exact ⟨by rw [hProgBody, hFormulaEq], hHeadT⟩

private theorem eo_prog_concat_cprop_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s tc,
      x1 = mkEq t s ∧ x2 = mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 t =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply notOp eqTerm =>
                      cases notOp with
                      | UOp notU =>
                          cases notU with
                          | not =>
                              cases eqTerm with
                              | Apply lhs2 zero =>
                                  cases lhs2 with
                                  | Apply op2 lenTerm =>
                                      cases op2 with
                                      | UOp eqU =>
                                          cases eqU with
                                          | eq =>
                                              cases lenTerm with
                                              | Apply lenOp tc =>
                                                  cases lenOp with
                                                  | UOp lenU =>
                                                      cases lenU with
                                                      | str_len =>
                                                          cases zero with
                                                          | Numeral z =>
                                                              by_cases hz : z = 0
                                                              · subst z
                                                                exact
                                                                  ⟨t, rhs1, tc,
                                                                    rfl, rfl⟩
                                                              · cases rev <;>
                                                                  simp [__eo_prog_concat_cprop, hz]
                                                                    at hProg
                                                          | _ =>
                                                              cases rev <;>
                                                                simp [__eo_prog_concat_cprop]
                                                                  at hProg
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_cprop]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_cprop]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_cprop]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_cprop] at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_cprop] at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_cprop] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_cprop] at hProg
                          | _ =>
                              cases rev <;>
                                simp [__eo_prog_concat_cprop] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_cprop] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_cprop] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_cprop] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_cprop] at hProg

private theorem concatCProp_rev_cases_of_prog_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htcNe : tc ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck rev t s tc hProg with
    ⟨_, hHeadT⟩
  have hHeadNe : concatCPropHead rev t ≠ Term.Stuck := by
    rw [hHeadT]
    exact htcNe
  have hNormNe : concatCPropNormalize rev t ≠ Term.Stuck :=
    concatSplitNormalize_ne_stuck_of_head_ne_stuck rev t hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (__str_nary_intro t) ≠ Term.Stuck := by
    simpa [concatCPropNormalize, concatSplitNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
    (__str_nary_intro t) hIteNe

private theorem cprop_formula_false_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropFormula (Term.Boolean false) t s tc ≠ Term.Stuck := by
  rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
    (Term.Boolean false) t s tc hProg).1]
  exact hProg

private theorem cprop_formula_true_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropFormula (Term.Boolean true) t s tc ≠ Term.Stuck := by
  rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
    (Term.Boolean true) t s tc hProg).1]
  exact hProg

private theorem cprop_prefix_false_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck := by
  have hFormulaNe := cprop_formula_false_ne_of_prog t s tc hProg
  have hRhsNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropPrefix (Term.Boolean false) t s))
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropSuffix (Term.Boolean false) t s tc))
            (__eo_nil (Term.UOp UserOp.str_concat)
              (__eo_typeof (concatCPropPrefix (Term.Boolean false) t s)))) ≠
        Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by
        simpa [concatCPropFormula, eo_ite_false] using hFormulaNe)
  have hFunNe :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
  exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFunNe

private theorem cprop_reverse_end_true_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck := by
  have hFormulaNe := cprop_formula_true_ne_of_prog t s tc hProg
  have hRhsNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropReverseSuffix (Term.Boolean true) t s tc))
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropReverseEnd (Term.Boolean true) t s))
            (__eo_nil (Term.UOp UserOp.str_concat)
              (__eo_typeof
                (concatCPropReverseSuffix (Term.Boolean true) t s tc)))) ≠
        Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by
        simpa [concatCPropFormula, eo_ite_true] using hFormulaNe)
  have hInnerNe :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hInnerFunNe :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInnerNe
  exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe

private theorem cprop_context_false_head_type
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof
            (__eo_to_smt (concatCPropHead (Term.Boolean false) s)) =
          SmtType.Seq T := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean false) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hPrefixNe :
      concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck :=
    cprop_prefix_false_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hPrefixNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
      hIntroT htcTy hTNN with
    ⟨htTy, _htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroS]
    simp
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hIntroSTy
    rw [hIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hIntroSConsTy with
    ⟨hscTy, _hsTailTy⟩
  exact ⟨T, htcTy, by simpa [sc] using hscTy⟩

private theorem cprop_overlap_len_false_int_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof (__eo_to_smt (concatCPropOverlapLen (Term.Boolean false) t s)) =
      SmtType.Int := by
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hKNe :
      concatCPropOverlapLen (Term.Boolean false) t s ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hPrefixNe
  exact smt_typeof_eo_add_one_of_ne_stuck
    (__str_overlap_rec (concatCPropSHeadTailWord (Term.Boolean false) s)
      (concatCPropFlatSecond (Term.Boolean false) t))
    (by simpa [concatCPropOverlapLen, eo_ite_false] using hKNe)

private theorem cprop_prefix_false_seq_type
    (t s tc : Term) (T : SmtType)
    (hscTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropHead (Term.Boolean false) s)) =
        SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
      SmtType.Seq T := by
  let sc := concatCPropHead (Term.Boolean false) s
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hOuterFun :
      __eo_mk_apply
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0)) k ≠ Term.Stuck := by
    simpa [concatCPropPrefix, sc, k] using hPrefixNe
  have hKNe : k ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOuterFun
  have hMidFunNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
        (Term.Numeral 0) ≠ Term.Stuck :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
  have hInnerFunNe :
      __eo_mk_apply (Term.UOp UserOp.str_substr) sc ≠ Term.Stuck :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMidFunNe
  have hscNe : sc ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe
  have hKTy :
      __smtx_typeof (__eo_to_smt k) = SmtType.Int := by
    simpa [k] using cprop_overlap_len_false_int_of_prog t s tc hProg
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_2]
  have hPrefixEq :
      concatCPropPrefix (Term.Boolean false) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0)) k := by
    simp [concatCPropPrefix, sc, k, __eo_mk_apply]
  rw [hPrefixEq]
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
          (__eo_to_smt k)) =
      SmtType.Seq T
  exact smtx_typeof_str_substr_seq (__eo_to_smt sc) (SmtTerm.Numeral 0)
    (__eo_to_smt k) T (by simpa [sc] using hscTy) hZeroTy hKTy

private theorem cprop_suffix_false_seq_type
    (t s tc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hPrefixTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatCPropSuffix (Term.Boolean false) t s tc)) =
      SmtType.Seq T := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  have hpfxNe : pfx ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck pfx T (by simpa [pfx] using hPrefixTy)
  have hLenPfxEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx =
        Term.Apply (Term.UOp UserOp.str_len) pfx :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) pfx (by simp) hpfxNe
  have hLenPfxNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx ≠ Term.Stuck := by
    rw [hLenPfxEq]
    simp
  have hSubMidEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) tc)
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hSubMidNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) ≠ Term.Stuck := by
    rw [hSubMidEq]
    simp
  have hNegLenEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hNegLenNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) ≠ Term.Stuck := by
    rw [hNegLenEq]
    simp
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Apply (Term.UOp UserOp.str_len) pfx))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) pfx)) := by
    rw [hSubMidEq, hNegLenEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Apply (Term.UOp UserOp.str_len) pfx))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) pfx)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropSuffix (Term.Boolean false) t s tc =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Apply (Term.UOp UserOp.str_len) pfx))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) pfx))) := by
    dsimp [concatCPropSuffix, pfx]
    rw [hOuterEq]
  have hLenTcTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt tc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt tc) T htcTy
  have hLenPfxTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt pfx)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt pfx) T (by simpa [pfx] using hPrefixTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt pfx))) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt tc))
      (SmtTerm.str_len (__eo_to_smt pfx)) hLenTcTy hLenPfxTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx)))) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tc)
      (SmtTerm.str_len (__eo_to_smt pfx))
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
        (SmtTerm.str_len (__eo_to_smt pfx))) T htcTy hLenPfxTy hNegTy
  rw [hSuffixEq]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx))))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using hSubTy

private theorem cprop_context_false
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tTail sTail,
      sc = concatCPropHead (Term.Boolean false) s ∧
      __str_nary_intro t = mkConcat tc tTail ∧
      __str_nary_intro s = mkConcat sc sTail ∧
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean false) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hFormulaNe : concatCPropFormula (Term.Boolean false) t s tc ≠ Term.Stuck := by
    rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg).1]
    exact hProg
  have hPrefixNe :
      concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck := by
    have hRhsNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropPrefix (Term.Boolean false) t s))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat)
                (concatCPropSuffix (Term.Boolean false) t s tc))
              (__eo_nil (Term.UOp UserOp.str_concat)
                (__eo_typeof (concatCPropPrefix (Term.Boolean false) t s)))) ≠
          Term.Stuck :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
        (by
          simpa [concatCPropFormula, eo_ite_false] using hFormulaNe)
    have hFunNe :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFunNe
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hPrefixNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
      hIntroT htcTy hTNN with
    ⟨htTy, htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroS]
    simp
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hIntroSTy
    rw [hIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hIntroSConsTy with
    ⟨hscTy, hsTailTy⟩
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck := by
    rw [hIntroT]
    simp
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T := by
    rw [hIntroT]
    exact smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
  have hIntroBool :
      RuleProofs.eo_has_bool_type
        (mkEq (__str_nary_intro t) (__str_nary_intro s)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroTTy, hIntroSTy]
    · rw [hIntroTTy]
      exact seq_ne_none T
  have hIntroEq :
      eo_interprets M (mkEq (__str_nary_intro t) (__str_nary_intro s)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM t s T htTy hsTy
      hIntroTNe hIntroSNe hST hIntroBool
  have hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
    simpa [hIntroT, hIntroS] using hIntroEq
  exact ⟨T, sc, tTail, sTail, rfl, hIntroT, hIntroS, hTTailList,
    hSTailList, htcTy, hscTy, htTailTy, hsTailTy, hConcatEq⟩

private theorem cprop_context_true
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tPrefix sPrefix tTail sTail,
      sc = concatCPropHead (Term.Boolean true) s ∧
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail ∧
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat sc sTail ∧
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean true) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hFormulaNe : concatCPropFormula (Term.Boolean true) t s tc ≠ Term.Stuck := by
    rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg).1]
    exact hProg
  have hReverseEndNe :
      concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck := by
    have hRhsNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropReverseSuffix (Term.Boolean true) t s tc))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat)
                (concatCPropReverseEnd (Term.Boolean true) t s))
              (__eo_nil (Term.UOp UserOp.str_concat)
                (__eo_typeof
                  (concatCPropReverseSuffix (Term.Boolean true) t s tc)))) ≠
          Term.Stuck :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
        (by
          simpa [concatCPropFormula, eo_ite_true] using hFormulaNe)
    have hInnerNe :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsNe
    have hInnerFunNe :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInnerNe
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hReverseEndNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      tc hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
      hRevIntroT htcTy hTNN with
    ⟨htTy, htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hRevIntroTNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck := by
    rw [hRevIntroT]
    simp
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntroTNe
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt t) T htTy with
    ⟨hTInh, hTWf⟩
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf t T htTy hTInh hTWf
      hIntroTNe
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  have hRevIntroSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevIntroSNe
  have hRevIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hRevIntroSTy
    rw [hRevIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hRevIntroSConsTy with
    ⟨hscTy, hsTailTy⟩
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroTNe
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroSNe
  have hDoubleT :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroTNe hRevIntroTNe
  have hDoubleS :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroSNe hRevIntroSNe
  have hDoubleEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))) true :=
    eo_interprets_double_rev_intros_of_elim_intros M hM t s T htTy hsTy
      hIntroTNN hIntroSNN hIntroTNe hIntroSNe hElimIntroT
      hElimIntroS hDoubleT hDoubleS hST
  have hRevConcatEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat tc tTail)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true := by
    simpa [hRevIntroT, hRevIntroS] using hDoubleEq
  have hConsTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat tc tTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      tc tTail (by decide) hTTailList
  have hConsSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat sc sTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      sc sTail (by decide) hSTailList
  have hConsTTy :
      __smtx_typeof (__eo_to_smt (mkConcat tc tTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
  have hConsSTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc sTail T hscTy hsTailTy
  have hRevConsT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat tc tTail) hConsTList
  have hRevConsS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat sc sTail) hConsSList
  have hElimConsT :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat tc tTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq tc tTail T
      hConsTTy hRevConsT
  have hElimConsS :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat sc sTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq sc sTail T
      hConsSTy hRevConsS
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM tc tTail T
      htcTy hTTailList htTailTy hRevConsT hElimConsT with
    ⟨tPrefix, htPrefixTy, hSnocT⟩
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM sc sTail T
      hscTy hSTailList hsTailTy hRevConsS hElimConsS with
    ⟨sPrefix, hsPrefixTy, hSnocS⟩
  have hSnocTSymm :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat tc tTail)))) true :=
    eo_interprets_eq_symm_local M
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (mkConcat tPrefix tc) hSnocT
  have hLeftToRight :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      hSnocTSymm hRevConcatEq
  have hSnocEq :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      (mkConcat sPrefix sc) hLeftToRight hSnocS
  exact ⟨T, sc, tPrefix, sPrefix, tTail, sTail, rfl, hRevIntroT,
    hRevIntroS, hTTailList, hSTailList, htcTy, hscTy, htPrefixTy,
    hsPrefixTy, hSnocEq⟩

private theorem cprop_context_true_head_type
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof
            (__eo_to_smt (concatCPropHead (Term.Boolean true) s)) =
          SmtType.Seq T := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean true) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hReverseEndNe :
      concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck :=
    cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hReverseEndNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      tc hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
      hRevIntroT htcTy hTNN with
    ⟨htTy, _htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  have hRevIntroSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevIntroSNe
  have hRevIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hRevIntroSTy
    rw [hRevIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hRevIntroSConsTy with
    ⟨hscTy, _hsTailTy⟩
  exact ⟨T, htcTy, by simpa [sc] using hscTy⟩

private theorem cprop_overlap_len_true_int_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof (__eo_to_smt (concatCPropOverlapLen (Term.Boolean true) t s)) =
      SmtType.Int := by
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hKNe :
      concatCPropOverlapLen (Term.Boolean true) t s ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEndNe
  exact smt_typeof_eo_add_one_of_ne_stuck
    (__str_overlap_rec
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (concatCPropSHeadTailWord (Term.Boolean true) s))
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (concatCPropFlatSecond (Term.Boolean true) t)))
    (by simpa [concatCPropOverlapLen, eo_ite_true] using hKNe)

private theorem cprop_reverse_end_true_seq_type
    (t s tc : Term) (T : SmtType)
    (hscTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropHead (Term.Boolean true) s)) =
        SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
      SmtType.Seq T := by
  let sc := concatCPropHead (Term.Boolean true) s
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T (by simpa [sc] using hscTy)
  have hKNe : k ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEndNe
  have hKTy : __smtx_typeof (__eo_to_smt k) = SmtType.Int := by
    simpa [k] using cprop_overlap_len_true_int_of_prog t s tc hProg
  have hLenScEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) sc =
        Term.Apply (Term.UOp UserOp.str_len) sc :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) sc (by simp) hscNe
  have hLenScNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) sc ≠ Term.Stuck := by
    rw [hLenScEq]
    simp
  have hSubFunEq :
      __eo_mk_apply (Term.UOp UserOp.str_substr) sc =
        Term.Apply (Term.UOp UserOp.str_substr) sc :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_substr) sc (by simp) hscNe
  have hNegFunEq :
      __eo_mk_apply (Term.UOp UserOp.neg)
          (__eo_mk_apply (Term.UOp UserOp.str_len) sc) =
        Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) sc) := by
    rw [hLenScEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) sc)
      (by simp) (by simp)
  have hNegEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) sc)) k := by
    rw [hNegFunEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) sc)) k
      (by simp) hKNe
  have hNegNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k ≠
        Term.Stuck := by
    rw [hNegEq]
    simp
  have hSubMidEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.neg)
              (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_substr) sc)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) sc)) k) := by
    rw [hSubFunEq, hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) sc)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) sc)) k)
      (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.neg)
                (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k)) k =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k := by
    rw [hSubMidEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.str_substr) sc)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k
      (by simp) hKNe
  have hEndEq :
      concatCPropReverseEnd (Term.Boolean true) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k := by
    dsimp [concatCPropReverseEnd, sc, k]
    rw [hOuterEq]
  have hLenScTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt sc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt sc) T (by simpa [sc] using hscTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k)) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k)
      hLenScTy hKTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt sc)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
            (__eo_to_smt k)) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt sc)
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
      (__eo_to_smt k) T (by simpa [sc] using hscTy) hNegTy hKTy
  rw [hEndEq]
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt sc)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
          (__eo_to_smt k)) =
      SmtType.Seq T
  exact hSubTy

private theorem cprop_reverse_suffix_true_seq_type
    (t s tc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hEndTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatCPropReverseSuffix (Term.Boolean true) t s tc)) =
      SmtType.Seq T := by
  let endPart := concatCPropReverseEnd (Term.Boolean true) t s
  have hEndNe : endPart ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck endPart T (by simpa [endPart] using hEndTy)
  have hLenEndEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart =
        Term.Apply (Term.UOp UserOp.str_len) endPart :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) endPart (by simp) hEndNe
  have hLenEndNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart ≠ Term.Stuck := by
    rw [hLenEndEq]
    simp
  have hNegEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart) := by
    rw [hLenEndEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) endPart) (by simp) (by simp)
  have hNegNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) ≠
        Term.Stuck := by
    rw [hNegEq]
    simp
  have hOuterEq :
      __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) endPart)) := by
    rw [hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) endPart)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropReverseSuffix (Term.Boolean true) t s tc =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart))) := by
    change
      Term.UOp1 UserOp1._at_purify
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart))) =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart)))
    rw [hOuterEq]
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_2]
  have hLenTcTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt tc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt tc) T htcTy
  have hLenEndTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt endPart)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt endPart) T
      (by simpa [endPart] using hEndTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt endPart))) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt tc))
      (SmtTerm.str_len (__eo_to_smt endPart)) hLenTcTy hLenEndTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart)))) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tc) (SmtTerm.Numeral 0)
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
        (SmtTerm.str_len (__eo_to_smt endPart))) T htcTy hZeroTy hNegTy
  rw [hSuffixEq]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart))))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using hSubTy

private theorem cprop_suffix_false_eval_of_prefix_eval
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc : Term) (T : SmtType) (st spfx : SmtSeq)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hPrefixTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtType.Seq T)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hPrefixEval :
      __smtx_model_eval M
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtValue.Seq spfx)
    (hle : (native_unpack_seq spfx).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropSuffix (Term.Boolean false) t s tc)) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).drop (native_unpack_seq spfx).length)) := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  have hpfxNe : pfx ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck pfx T (by simpa [pfx] using hPrefixTy)
  have hLenPfxEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx =
        Term.Apply (Term.UOp UserOp.str_len) pfx :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) pfx (by simp) hpfxNe
  have hSubMidEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) tc)
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hNegLenEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Apply (Term.UOp UserOp.str_len) pfx))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) pfx)) := by
    rw [hSubMidEq, hNegLenEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Apply (Term.UOp UserOp.str_len) pfx))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) pfx)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropSuffix (Term.Boolean false) t s tc =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Apply (Term.UOp UserOp.str_len) pfx))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) pfx))) := by
    dsimp [concatCPropSuffix, pfx]
    rw [hOuterEq]
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hSub :
      native_seq_extract (native_unpack_seq st)
          (Int.ofNat (native_unpack_seq spfx).length)
          (Int.ofNat
            ((native_unpack_seq st).length - (native_unpack_seq spfx).length)) =
        (native_unpack_seq st).drop (native_unpack_seq spfx).length :=
    native_seq_extract_to_end_nat (native_unpack_seq st)
      (native_unpack_seq spfx).length hle
  have hDiff :
      Int.ofNat
          ((native_unpack_seq st).length - (native_unpack_seq spfx).length) =
        Int.ofNat (native_unpack_seq st).length -
          Int.ofNat (native_unpack_seq spfx).length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq st)
          (Int.ofNat (native_unpack_seq spfx).length)
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq spfx).length) =
        (native_unpack_seq st).drop (native_unpack_seq spfx).length := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [Int.sub_eq_add_neg] using hSub'
  rw [hSuffixEq]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx))))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).drop (native_unpack_seq spfx).length))
  simp [pfx, htcEval, hPrefixEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
    __smtx_model_eval__at_purify, __smtx_model_eval__,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

private theorem native_seq_extract_zero_nat_any
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n <= xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length <= n := Nat.le_of_lt hLenLt
        have hLenNotLe :
            ¬ ((Int.ofNat xs.length : Int) + 1 <= 0) := by
          have hNonneg : (0 : Int) <= Int.ofNat xs.length :=
            Int.natCast_nonneg xs.length
          omega
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat, List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

private theorem cprop_prefix_false_eval_of_overlap
    (M : SmtModel) (hM : model_total_typed M)
    (t s sc : Term) (T : SmtType) (ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat n)) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
      SmtValue.Seq
        (native_pack_seq T ((native_unpack_seq ss).take n)) := by
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T hscTy
  have hPrefixEq :
      concatCPropPrefix (Term.Boolean false) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0))
          (Term.Numeral (Int.ofNat n)) := by
    dsimp [concatCPropPrefix, k]
    rw [← hScEq, hOverlap]
    simp [__eo_mk_apply]
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have hSub :
      native_seq_extract (native_unpack_seq ss) 0 (Int.ofNat n) =
        (native_unpack_seq ss).take n :=
    native_seq_extract_zero_nat_any (native_unpack_seq ss) n
  rw [hPrefixEq]
  change
    __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
          (SmtTerm.Numeral (Int.ofNat n))) =
      SmtValue.Seq (native_pack_seq T ((native_unpack_seq ss).take n))
  simp [hscEval, __smtx_model_eval, __smtx_model_eval_str_substr,
    hElem]
  exact congrArg (native_pack_seq T) hSub

private theorem native_seq_extract_suffix_nat_suffix
    (xs : List SmtValue) (n : Nat) :
    ∃ pre,
      xs =
        pre ++
          native_seq_extract xs
            (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) := by
  by_cases hle : n <= xs.length
  · refine ⟨xs.take (xs.length - n), ?_⟩
    have hStart :
        Int.ofNat xs.length + -Int.ofNat n =
          Int.ofNat (xs.length - n) := by
      rw [← Int.sub_eq_add_neg]
      exact (Int.ofNat_sub hle).symm
    have hRem : xs.length - (xs.length - n) = n := by
      omega
    have hSub :=
      native_seq_extract_to_end_nat xs (xs.length - n)
        (Nat.sub_le xs.length n)
    rw [hRem] at hSub
    rw [hStart, hSub]
    exact (List.take_append_drop (xs.length - n) xs).symm
  · refine ⟨xs, ?_⟩
    have hlt : xs.length < n := Nat.lt_of_not_ge hle
    have hltInt : (Int.ofNat xs.length : Int) < Int.ofNat n :=
      Int.ofNat_lt.mpr hlt
    have hStartNeg :
        Int.ofNat xs.length + -Int.ofNat n < 0 := by
      omega
    have hExtract :
        native_seq_extract xs
          (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) = [] := by
      unfold native_seq_extract
      have hGuard :
          (decide (Int.ofNat xs.length + -Int.ofNat n < 0) ||
                decide (Int.ofNat n <= 0) ||
              decide
                (Int.ofNat xs.length + -Int.ofNat n >=
                  Int.ofNat xs.length)) =
            true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (Or.inl hStartNeg)
      rw [if_pos hGuard]
    rw [hExtract]
    simp

private theorem native_seq_extract_length_le_nat_arg
    (xs : List SmtValue) (i : native_Int) (n : Nat) :
    (native_seq_extract xs i (Int.ofNat n)).length <= n := by
  have hInt :
      Int.ofNat (native_seq_extract xs i (Int.ofNat n)).length <=
        Int.ofNat n := by
    simp only [native_seq_extract]
    split
    · simp
    · rename_i h
      have hProp :
          ¬ ((i < 0 ∨ Int.ofNat n <= 0) ∨
              Int.ofNat xs.length <= i) := by
        simpa [Bool.or_eq_true, decide_eq_true_eq] using h
      have hiNonneg : 0 <= i := by
        have hiNot : ¬ i < 0 := by
          intro hi
          exact hProp (Or.inl (Or.inl hi))
        exact Int.le_of_not_gt hiNot
      have hiLt : i < Int.ofNat xs.length := by
        have hiNot : ¬ Int.ofNat xs.length <= i := by
          intro hle
          exact hProp (Or.inr hle)
        exact Int.lt_of_not_ge hiNot
      have hTake :
          ((xs.drop (Int.toNat i)).take
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i)))).length <=
            Int.toNat (min (Int.ofNat n) (Int.ofNat xs.length - i)) :=
        List.length_take_le _ _
      have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by
        omega
      have hMinNonneg :
          0 <= min (Int.ofNat n) (Int.ofNat xs.length - i) := by
        exact (Int.le_min).2 ⟨Int.natCast_nonneg n, hDiffNonneg⟩
      have hCast :
          Int.ofNat
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i))) =
            min (Int.ofNat n) (Int.ofNat xs.length - i) :=
        Int.toNat_of_nonneg hMinNonneg
      have hLenLe :
          Int.ofNat
              ((xs.drop (Int.toNat i)).take
                (Int.toNat
                  (min (Int.ofNat n)
                    (Int.ofNat xs.length - i)))).length <=
            Int.ofNat
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i))) :=
        Int.ofNat_le.mpr hTake
      have hMinLe :
          min (Int.ofNat n) (Int.ofNat xs.length - i) <=
            Int.ofNat n :=
        Int.min_le_left _ _
      omega
  exact Int.ofNat_le.mp hInt

private theorem cprop_reverse_end_true_eval_of_overlap
    (M : SmtModel) (hM : model_total_typed M)
    (t s sc : Term) (T : SmtType) (ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat n)) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
      SmtValue.Seq
        (native_pack_seq T
          (native_seq_extract (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
            (Int.ofNat n))) := by
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T hscTy
  have hEndEq :
      concatCPropReverseEnd (Term.Boolean true) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc))
              (Term.Numeral (Int.ofNat n))))
          (Term.Numeral (Int.ofNat n)) := by
    dsimp [concatCPropReverseEnd, k]
    rw [← hScEq, hOverlap]
    simp [__eo_mk_apply]
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  rw [hEndEq]
  change
    __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt sc)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
            (SmtTerm.Numeral (Int.ofNat n)))
          (SmtTerm.Numeral (Int.ofNat n))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_seq_extract (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
            (Int.ofNat n)))
  simp [hscEval, __smtx_model_eval, __smtx_model_eval_str_len,
    __smtx_model_eval_str_substr, __smtx_model_eval__, native_seq_len,
    native_zplus, native_zneg, hElem]

private theorem cprop_reverse_suffix_true_eval_of_end_eval
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc : Term) (T : SmtType) (st send : SmtSeq)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hEndTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtType.Seq T)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hEndEval :
      __smtx_model_eval M
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtValue.Seq send)
    (hle : (native_unpack_seq send).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropReverseSuffix (Term.Boolean true) t s tc)) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - (native_unpack_seq send).length))) := by
  let endPart := concatCPropReverseEnd (Term.Boolean true) t s
  have hEndNe : endPart ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck endPart T (by simpa [endPart] using hEndTy)
  have hLenEndEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart =
        Term.Apply (Term.UOp UserOp.str_len) endPart :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) endPart (by simp) hEndNe
  have hNegEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart) := by
    rw [hLenEndEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) endPart) (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) endPart)) := by
    rw [hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) endPart)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropReverseSuffix (Term.Boolean true) t s tc =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart))) := by
    change
      Term.UOp1 UserOp1._at_purify
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart))) =
        Term.UOp1 UserOp1._at_purify
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart)))
    rw [hOuterEq]
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hSub :
      native_seq_extract (native_unpack_seq st) 0
          (Int.ofNat
            ((native_unpack_seq st).length - (native_unpack_seq send).length)) =
        (native_unpack_seq st).take
          ((native_unpack_seq st).length - (native_unpack_seq send).length) :=
    native_seq_extract_zero_nat (native_unpack_seq st)
      ((native_unpack_seq st).length - (native_unpack_seq send).length)
      (Nat.sub_le _ _)
  have hDiff :
      Int.ofNat
          ((native_unpack_seq st).length - (native_unpack_seq send).length) =
        Int.ofNat (native_unpack_seq st).length -
          Int.ofNat (native_unpack_seq send).length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq st) 0
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq send).length) =
        (native_unpack_seq st).take
          ((native_unpack_seq st).length - (native_unpack_seq send).length) := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [Int.sub_eq_add_neg] using hSub'
  rw [hSuffixEq]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart))))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - (native_unpack_seq send).length)))
  simp [endPart, htcEval, hEndEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
    __smtx_model_eval__at_purify, __smtx_model_eval__,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

private theorem cprop_length_ne_zero_of_not_len_eq_eval
    (M : SmtModel) (u : Term) (su : SmtSeq)
    (huEval : __smtx_model_eval M (__eo_to_smt u) = SmtValue.Seq su)
    (hLenNe :
      eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true) :
    (native_unpack_seq su).length ≠ 0 := by
  have hEqFalse :
      eo_interprets M (mkEq (mkStrLen u) (Term.Numeral 0)) false :=
    RuleProofs.eo_interprets_not_true_implies_false M
      (mkEq (mkStrLen u) (Term.Numeral 0)) hLenNe
  have hEval :
      __smtx_model_eval M (__eo_to_smt (mkEq (mkStrLen u) (Term.Numeral 0))) =
        SmtValue.Boolean false := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (mkEq (mkStrLen u) (Term.Numeral 0)) false).mp hEqFalse with
    | intro_false _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt u)) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean false at hEval
  rw [__smtx_model_eval.eq_134] at hEval
  rw [__smtx_model_eval.eq_79] at hEval
  simp [huEval, __smtx_model_eval_str_len, __smtx_model_eval_eq,
    __smtx_model_eval, native_seq_len, native_veq] at hEval
  intro hLen
  apply hEval
  exact List.eq_nil_of_length_eq_zero hLen

private theorem cprop_false_formula_of_overlap_bounds
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc sc tTail sTail : Term) (T : SmtType)
    (st stail ss sstail : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (htTailEval :
      __smtx_model_eval M (__eo_to_smt tTail) = SmtValue.Seq stail)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hsTailEval :
      __smtx_model_eval M (__eo_to_smt sTail) = SmtValue.Seq sstail)
    (hAppend :
      native_unpack_seq st ++ native_unpack_seq stail =
        native_unpack_seq ss ++ native_unpack_seq sstail)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat n))
    (hnPfx :
      ((native_unpack_seq ss).take n).length <=
        (native_unpack_seq st).length) :
    eo_interprets M (concatCPropFormula (Term.Boolean false) t s tc) true := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  let sfx := concatCPropSuffix (Term.Boolean false) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
  let tail := mkConcat sfx nil
  let rhs := mkConcat pfx tail
  have hPfxTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [pfx, hScEq] using cprop_prefix_false_seq_type t s tc T
      (by simpa [hScEq] using hscTy) hProg
  have hSfxTy : __smtx_typeof (__eo_to_smt sfx) = SmtType.Seq T := by
    simpa [sfx] using cprop_suffix_false_seq_type t s tc T htcTy hPfxTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq pfx T hPfxTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq sfx nil T hSfxTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq pfx tail T hPfxTy hTailTy
  have hpfxEval :
      __smtx_model_eval M (__eo_to_smt pfx) =
        SmtValue.Seq (native_pack_seq T ((native_unpack_seq ss).take n)) := by
    simpa [pfx] using cprop_prefix_false_eval_of_overlap M hM t s sc T ss n
      hScEq hscTy hscEval hOverlap
  have hsfxEval :
      __smtx_model_eval M (__eo_to_smt sfx) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).drop ((native_unpack_seq ss).take n).length)) := by
    have hDrop :
        (native_unpack_seq
              (native_pack_seq T ((native_unpack_seq ss).take n))).length <=
          (native_unpack_seq st).length := by
      simpa [native_unpack_pack_seq] using hnPfx
    have hEval :=
      cprop_suffix_false_eval_of_prefix_eval M hM t s tc T st
        (native_pack_seq T ((native_unpack_seq ss).take n)) htcTy
        (by simpa [pfx] using hPfxTy) htcEval (by simpa [pfx] using hpfxEval)
        hDrop
    simpa [sfx, native_unpack_pack_seq] using hEval
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M pfx T hPfxTy
  have hPfxElem :
      __smtx_elem_typeof_seq_value
          (native_pack_seq T ((native_unpack_seq ss).take n)) = T :=
    elem_typeof_pack_seq T ((native_unpack_seq ss).take n)
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq ss).take n ++
              (native_unpack_seq st).drop ((native_unpack_seq ss).take n).length ++
              native_unpack_seq (SmtSeq.empty T))) := by
    simpa [rhs, tail, native_unpack_pack_seq] using
      eval_mkConcat_right_nested M pfx sfx nil T
        (native_pack_seq T ((native_unpack_seq ss).take n))
        (native_pack_seq T
          ((native_unpack_seq st).drop ((native_unpack_seq ss).take n).length))
        (SmtSeq.empty T) hpfxEval hsfxEval hNilEval hPfxElem
  have hTakeEq :
      (native_unpack_seq ss).take n =
        (native_unpack_seq st).take ((native_unpack_seq ss).take n).length := by
    let p := ((native_unpack_seq ss).take n).length
    have hpSs : p <= (native_unpack_seq ss).length := by
      simp [p, List.length_take]
      exact Nat.min_le_right n (native_unpack_seq ss).length
    have hTakeSsP :
        (native_unpack_seq ss).take p = (native_unpack_seq ss).take n := by
      let xs := native_unpack_seq ss
      change xs.take (xs.take n).length = xs.take n
      by_cases hle : n <= xs.length
      · have hLen : (xs.take n).length = n := by
          simp [List.length_take, Nat.min_eq_left hle]
        rw [hLen]
      · have hLenLe : xs.length <= n :=
          Nat.le_of_lt (Nat.lt_of_not_ge hle)
        have hLen : (xs.take n).length = xs.length := by
          simp [List.length_take, Nat.min_eq_right hLenLe]
        rw [hLen, List.take_of_length_le (Nat.le_refl xs.length),
          List.take_of_length_le hLenLe]
    have hTake := congrArg (List.take p) hAppend
    rw [List.take_append_of_le_length hnPfx,
      List.take_append_of_le_length hpSs] at hTake
    exact (hTake.trans hTakeSsP).symm
  have hRhsEvalTc :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T (native_unpack_seq st)) := by
    let p := ((native_unpack_seq ss).take n).length
    have hList :
        (native_unpack_seq ss).take n ++
            (native_unpack_seq st).drop ((native_unpack_seq ss).take n).length ++
            native_unpack_seq (SmtSeq.empty T) =
          native_unpack_seq st := by
      change
        ((native_unpack_seq ss).take n ++
            (native_unpack_seq st).drop p) ++ [] =
          native_unpack_seq st
      rw [hTakeEq]
      change
        ((native_unpack_seq st).take p ++
            (native_unpack_seq st).drop p) ++ [] =
          native_unpack_seq st
      simp [List.take_append_drop]
    rw [hRhsEval]
    exact congrArg SmtValue.Seq (congrArg (native_pack_seq T) hList)
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [htcEval, hRhsEvalTc]
    change RuleProofs.smt_seq_rel st (native_pack_seq T (native_unpack_seq st))
    have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
      have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
        (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
      simpa [htcEval, __smtx_typeof_value] using htcValTy
    exact smt_seq_rel_pack_unpack T st
      (elem_typeof_seq_value_of_typeof_seq_value hstTy)
  have hEqTrue : eo_interprets M (mkEq tc rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhs hEqBool hRel
  have hpfxNe : pfx ≠ Term.Stuck := cprop_seq_type_ne_stuck pfx T hPfxTy
  have hsfxNe : sfx ≠ Term.Stuck := cprop_seq_type_ne_stuck sfx T hSfxTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) sfx =
          Term.Apply (Term.UOp UserOp.str_concat) sfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) sfx (by simp) hsfxNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) sfx) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) pfx =
          Term.Apply (Term.UOp UserOp.str_concat) pfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) pfx (by simp) hpfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) pfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean false) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_false, pfx, sfx, nil] using hEqGenEq
  simpa [hFormulaEq] using hEqTrue

private theorem cprop_true_formula_of_overlap_bounds
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc sc tPrefix sPrefix : Term) (T : SmtType)
    (stp st ssp ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htPrefixEval :
      __smtx_model_eval M (__eo_to_smt tPrefix) = SmtValue.Seq stp)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hsPrefixEval :
      __smtx_model_eval M (__eo_to_smt sPrefix) = SmtValue.Seq ssp)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hAppend :
      native_unpack_seq stp ++ native_unpack_seq st =
        native_unpack_seq ssp ++ native_unpack_seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat n))
    (hnEnd :
      (native_seq_extract (native_unpack_seq ss)
          (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
          (Int.ofNat n)).length <=
        (native_unpack_seq st).length) :
    eo_interprets M (concatCPropFormula (Term.Boolean true) t s tc) true := by
  let rEnd := concatCPropReverseEnd (Term.Boolean true) t s
  let rSfx := concatCPropReverseSuffix (Term.Boolean true) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof rSfx)
  let tail := mkConcat rEnd nil
  let rhs := mkConcat rSfx tail
  let endList :=
    native_seq_extract (native_unpack_seq ss)
      (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n) (Int.ofNat n)
  have hEndTy : __smtx_typeof (__eo_to_smt rEnd) = SmtType.Seq T := by
    simpa [rEnd] using cprop_reverse_end_true_seq_type t s tc T
      (by simpa [hScEq] using hscTy) hProg
  have hSfxTy : __smtx_typeof (__eo_to_smt rSfx) = SmtType.Seq T := by
    simpa [rSfx] using cprop_reverse_suffix_true_seq_type t s tc T
      htcTy hEndTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq rSfx T hSfxTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq rEnd nil T hEndTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq rSfx tail T hSfxTy hTailTy
  have hEndEval :
      __smtx_model_eval M (__eo_to_smt rEnd) =
        SmtValue.Seq (native_pack_seq T endList) := by
    simpa [rEnd, endList] using
      cprop_reverse_end_true_eval_of_overlap M hM t s sc T ss n
        hScEq hscTy hscEval hOverlap
  have hSfxEval :
      __smtx_model_eval M (__eo_to_smt rSfx) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length))) := by
    have hEndDrop :
        (native_unpack_seq (native_pack_seq T endList)).length <=
          (native_unpack_seq st).length := by
      simpa [endList, native_unpack_pack_seq] using hnEnd
    have hEval :=
      cprop_reverse_suffix_true_eval_of_end_eval M hM t s tc T st
        (native_pack_seq T endList) htcTy hEndTy htcEval
        (by simpa [rEnd, endList] using hEndEval) hEndDrop
    simpa [rSfx, endList, native_unpack_pack_seq] using hEval
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M rSfx T hSfxTy
  have hSfxElem :
      __smtx_elem_typeof_seq_value
          (native_pack_seq T
            ((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length))) = T :=
    elem_typeof_pack_seq T
      ((native_unpack_seq st).take
        ((native_unpack_seq st).length - endList.length))
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).take
                ((native_unpack_seq st).length - endList.length) ++
              endList ++ native_unpack_seq (SmtSeq.empty T))) := by
    simpa [rhs, tail, native_unpack_pack_seq] using
      eval_mkConcat_right_nested M rSfx rEnd nil T
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length)))
        (native_pack_seq T endList) (SmtSeq.empty T) hSfxEval hEndEval
        hNilEval hSfxElem
  rcases native_seq_extract_suffix_nat_suffix (native_unpack_seq ss) n with
    ⟨ssPre, hSsPre⟩
  have hSuffixSt :
      native_unpack_seq st =
        (native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length) ++
          endList := by
    have hAppendEnd :
        native_unpack_seq stp ++ native_unpack_seq st =
          (native_unpack_seq ssp ++ ssPre) ++ endList := by
      rw [hAppend]
      change
        native_unpack_seq ssp ++ native_unpack_seq ss =
          (native_unpack_seq ssp ++ ssPre) ++ endList
      rw [hSsPre]
      simp [List.append_assoc, endList]
    exact concat_split_suffix_eq_take_append_of_append_eq_of_le
      (native_unpack_seq stp) (native_unpack_seq st)
      (native_unpack_seq ssp ++ ssPre) endList hAppendEnd hnEnd
  have hRhsEvalTc :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T (native_unpack_seq st)) := by
    have hList :
        (native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length) ++
          endList ++ native_unpack_seq (SmtSeq.empty T) =
        native_unpack_seq st := by
      change
        (((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length) ++
            endList) ++ []) =
          native_unpack_seq st
      rw [← hSuffixSt]
      simp
    rw [hRhsEval]
    exact congrArg SmtValue.Seq (congrArg (native_pack_seq T) hList)
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [htcEval, hRhsEvalTc]
    change RuleProofs.smt_seq_rel st (native_pack_seq T (native_unpack_seq st))
    have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
      have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
        (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
      simpa [htcEval, __smtx_typeof_value] using htcValTy
    exact smt_seq_rel_pack_unpack T st
      (elem_typeof_seq_value_of_typeof_seq_value hstTy)
  have hEqTrue : eo_interprets M (mkEq tc rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhs hEqBool hRel
  have hSfxNe : rSfx ≠ Term.Stuck := cprop_seq_type_ne_stuck rSfx T hSfxTy
  have hEndNe : rEnd ≠ Term.Stuck := cprop_seq_type_ne_stuck rEnd T hEndTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rEnd =
          Term.Apply (Term.UOp UserOp.str_concat) rEnd :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rEnd (by simp) hEndNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rEnd) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rSfx =
          Term.Apply (Term.UOp UserOp.str_concat) rSfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rSfx (by simp) hSfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rSfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean true) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_true, rSfx, rEnd, nil] using hEqGenEq
  simpa [hFormulaEq] using hEqTrue

private theorem facts_concat_cprop_false_formula
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc sc tTail sTail : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hIntroT : __str_nary_intro t = mkConcat tc tTail)
    (hIntroS : __str_nary_intro s = mkConcat sc sTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hSTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true) :
    eo_interprets M (concatCPropFormula (Term.Boolean false) t s tc) true := by
  rcases concat_split_append_eq_of_concat_eq M hM tc tTail sc sTail T
      htcTy htTailTy hscTy hsTailTy hConcatEq with
    ⟨st, stail, ss, sstail, htcEval, htTailEval, hscEval, hsTailEval,
      hAppend⟩
  have htcLenNe : (native_unpack_seq st).length ≠ 0 :=
    cprop_length_ne_zero_of_not_len_eq_eval M tc st htcEval hNonzero
  let recS := concatCPropSHeadTailWord (Term.Boolean false) s
  let recT := concatCPropFlatSecond (Term.Boolean false) t
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hKNe : k ≠ Term.Stuck := by
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by simpa [k, concatCPropPrefix] using hPrefixNe)
  have hRecNe : __str_overlap_rec recS recT ≠ Term.Stuck := by
    apply cprop_eo_add_one_arg_ne_stuck
    simpa [k, recS, recT, concatCPropOverlapLen, eo_ite_false] using hKNe
  have hRecSNe : recS ≠ Term.Stuck :=
    str_overlap_rec_left_ne_stuck_of_ne_stuck recS recT hRecNe
  have hRecTNe : recT ≠ Term.Stuck :=
    str_overlap_rec_right_ne_stuck_of_ne_stuck recS recT hRecNe
  rcases cprop_false_head_string_of_tailword_ne s sc T hScEq hscTy
      (by simpa [recS] using hRecSNe) with
    ⟨scWord, hScString⟩
  have hSsWord :
      native_unpack_seq ss = scWord.map SmtValue.Char := by
    exact string_eval_unpack_eq M scWord ss (by simpa [hScString] using hscEval)
  rcases cprop_flat_second_false_tail_head_of_ne_stuck t tc tTail
      hIntroT hTTailList (by simpa [recT] using hRecTNe) with
    ⟨tSecond, tSecondTail, hTTailHead, hTSecondTailList, hRecTEq⟩
  have htTailConsEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat tSecond tSecondTail)) =
        SmtValue.Seq stail := by
    simpa [hTTailHead] using htTailEval
  rcases strConcat_args_seq_eval_of_concat_seq_eval M tSecond tSecondTail
      ⟨stail, htTailConsEval⟩ with
    ⟨⟨stSecond, htSecondEval⟩,
      ⟨stSecondTail, htSecondTailEval⟩⟩
  have hStailSplit :
      native_unpack_seq stail =
        native_unpack_seq stSecond ++ native_unpack_seq stSecondTail :=
    mkConcat_eval_unpack_eq M tSecond tSecondTail stail stSecond
      stSecondTail htTailConsEval htSecondEval htSecondTailEval
  rcases str_overlap_rec_numeral_of_ne_stuck recS recT hRecNe with
    ⟨m, hRec⟩
  have hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat (m + 1)) := by
    simp [concatCPropOverlapLen, eo_ite_false, recS, recT, hRec, __eo_add,
      native_zplus]
    rw [Int.add_comm]
  have hnPfx :
      ((native_unpack_seq ss).take (m + 1)).length <=
        (native_unpack_seq st).length := by
    by_cases hleSS :
        (native_unpack_seq ss).length <= (native_unpack_seq st).length
    · have hTakeLeSS :
          ((native_unpack_seq ss).take (m + 1)).length <=
            (native_unpack_seq ss).length := by
        simp [List.length_take]
        exact Nat.min_le_right (m + 1) (native_unpack_seq ss).length
      exact Nat.le_trans hTakeLeSS hleSS
    · by_cases hGoal :
          ((native_unpack_seq ss).take (m + 1)).length <=
            (native_unpack_seq st).length
      · exact hGoal
      have hstPos : 0 < (native_unpack_seq st).length :=
        Nat.pos_of_ne_zero htcLenNe
      have hDropLt : (native_unpack_seq st).length - 1 < m := by
        have hTakeLen :
            ((native_unpack_seq ss).take (m + 1)).length =
              min (m + 1) (native_unpack_seq ss).length := by
          simp [List.length_take]
        rw [hTakeLen] at hGoal
        omega
      have hCompatFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT =
            Term.Boolean false :=
        str_overlap_rec_compatible_drop_false_of_lt recS recT m
          ((native_unpack_seq st).length - 1) hRec hDropLt
      have hCompatNotFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT ≠
            Term.Boolean false := by
        sorry
      exact False.elim (hCompatNotFalse hCompatFalse)
  exact cprop_false_formula_of_overlap_bounds M hM t s tc sc tTail sTail T
    st stail ss sstail (m + 1) hScEq htcTy hscTy htTailTy hsTailTy hProg
    htcEval htTailEval hscEval hsTailEval hAppend hOverlap hnPfx

private theorem facts_concat_cprop_true_formula
    (M : SmtModel) (hM : model_total_typed M)
    (t s tc sc tPrefix sPrefix tTail sTail : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hRevIntroT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail)
    (hRevIntroS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat sc sTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hSTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true) :
    eo_interprets M (concatCPropFormula (Term.Boolean true) t s tc) true := by
  rcases concat_split_append_eq_of_concat_eq M hM tPrefix tc sPrefix sc T
      htPrefixTy htcTy hsPrefixTy hscTy hConcatEq with
    ⟨stp, st, ssp, ss, htPrefixEval, htcEval, hsPrefixEval, hscEval,
      hAppend⟩
  have htcLenNe : (native_unpack_seq st).length ≠ 0 :=
    cprop_length_ne_zero_of_not_len_eq_eval M tc st htcEval hNonzero
  let recS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (concatCPropSHeadTailWord (Term.Boolean true) s)
  let recT :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (concatCPropFlatSecond (Term.Boolean true) t)
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hKNe : k ≠ Term.Stuck := by
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by simpa [k, concatCPropReverseEnd] using hEndNe)
  have hRecNe : __str_overlap_rec recS recT ≠ Term.Stuck := by
    apply cprop_eo_add_one_arg_ne_stuck
    simpa [k, recS, recT, concatCPropOverlapLen, eo_ite_true] using hKNe
  have hRecSNe : recS ≠ Term.Stuck :=
    str_overlap_rec_left_ne_stuck_of_ne_stuck recS recT hRecNe
  have hRecTNe : recT ≠ Term.Stuck :=
    str_overlap_rec_right_ne_stuck_of_ne_stuck recS recT hRecNe
  have hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean true) s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (concatCPropSHeadTailWord (Term.Boolean true) s)
      (by simpa [recS] using hRecSNe)
  rcases cprop_true_head_string_of_tailword_ne s sc T hScEq hscTy
      hTailWordNe with
    ⟨scWord, hScString⟩
  have hSsWord :
      native_unpack_seq ss = scWord.map SmtValue.Char := by
    exact string_eval_unpack_eq M scWord ss (by simpa [hScString] using hscEval)
  rcases cprop_flat_second_true_tail_head_of_rev_ne_stuck t tc tTail
      hRevIntroT hTTailList (by simpa [recT] using hRecTNe) with
    ⟨tSecond, tSecondTail, hTTailHead, hTSecondTailList, hFlatSecondEq⟩
  rcases str_overlap_rec_numeral_of_ne_stuck recS recT hRecNe with
    ⟨m, hRec⟩
  have hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat (m + 1)) := by
    simp [concatCPropOverlapLen, eo_ite_true, recS, recT, hRec, __eo_add,
      native_zplus]
    rw [Int.add_comm]
  have hnEnd :
      (native_seq_extract (native_unpack_seq ss)
          (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
          (Int.ofNat (m + 1))).length <=
        (native_unpack_seq st).length := by
    by_cases hleSS :
        (native_unpack_seq ss).length <= (native_unpack_seq st).length
    · rcases native_seq_extract_suffix_nat_suffix (native_unpack_seq ss)
          (m + 1) with
        ⟨pre, hSuffix⟩
      have hEndLeSS :
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
            (native_unpack_seq ss).length := by
        calc
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
              (pre ++
                native_seq_extract (native_unpack_seq ss)
                  (Int.ofNat (native_unpack_seq ss).length +
                    -Int.ofNat (m + 1))
                  (Int.ofNat (m + 1))).length := by
            simp
          _ = (native_unpack_seq ss).length := by
            exact (congrArg List.length hSuffix).symm
      exact Nat.le_trans hEndLeSS hleSS
    · by_cases hGoal :
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
            (native_unpack_seq st).length
      · exact hGoal
      have hstPos : 0 < (native_unpack_seq st).length :=
        Nat.pos_of_ne_zero htcLenNe
      have hDropLt : (native_unpack_seq st).length - 1 < m := by
        have hEndLeN :
            (native_seq_extract (native_unpack_seq ss)
                (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
                (Int.ofNat (m + 1))).length <=
              m + 1 :=
          native_seq_extract_length_le_nat_arg (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
            (m + 1)
        omega
      have hCompatFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT =
            Term.Boolean false :=
        str_overlap_rec_compatible_drop_false_of_lt recS recT m
          ((native_unpack_seq st).length - 1) hRec hDropLt
      have hCompatNotFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT ≠
            Term.Boolean false := by
        sorry
      exact False.elim (hCompatNotFalse hCompatFalse)
  exact cprop_true_formula_of_overlap_bounds M hM t s tc sc tPrefix
    sPrefix T stp st ssp ss (m + 1) hScEq htcTy hscTy htPrefixTy
    hsPrefixTy hProg htPrefixEval htcEval hsPrefixEval hscEval hAppend
    hOverlap hnEnd

private theorem concatCPropFormula_has_smt_translation_false
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (concatCPropFormula (Term.Boolean false) t s tc) := by
  rcases cprop_context_false_head_type t s tc hPremBool hNonzeroBool hProg with
    ⟨T, htcTy, hscTy⟩
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  let sfx := concatCPropSuffix (Term.Boolean false) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
  let tail := mkConcat sfx nil
  let rhs := mkConcat pfx tail
  have hPfxTy :
      __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [pfx] using cprop_prefix_false_seq_type t s tc T hscTy hProg
  have hSfxTy :
      __smtx_typeof (__eo_to_smt sfx) = SmtType.Seq T := by
    simpa [sfx] using cprop_suffix_false_seq_type t s tc T htcTy hPfxTy
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq pfx T hPfxTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq sfx nil T hSfxTy hNilTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq pfx tail T hPfxTy hTailTy
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hpfxNe : pfx ≠ Term.Stuck := cprop_seq_type_ne_stuck pfx T hPfxTy
  have hsfxNe : sfx ≠ Term.Stuck := cprop_seq_type_ne_stuck sfx T hSfxTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) sfx =
          Term.Apply (Term.UOp UserOp.str_concat) sfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) sfx (by simp) hsfxNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) sfx) nil
        (by simp) hnilNe
  have hTailGenNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil ≠
        Term.Stuck := by
    rw [hTailGenEq]
    simp [tail, mkConcat]
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) pfx =
          Term.Apply (Term.UOp UserOp.str_concat) pfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) pfx (by simp) hpfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) pfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean false) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_false, pfx, sfx, nil] using hEqGenEq
  rw [hFormulaEq]
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

private theorem concatCPropFormula_has_smt_translation_true
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (concatCPropFormula (Term.Boolean true) t s tc) := by
  rcases cprop_context_true_head_type t s tc hPremBool hNonzeroBool hProg with
    ⟨T, htcTy, hscTy⟩
  let rSfx := concatCPropReverseSuffix (Term.Boolean true) t s tc
  let rEnd := concatCPropReverseEnd (Term.Boolean true) t s
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof rSfx)
  let tail := mkConcat rEnd nil
  let rhs := mkConcat rSfx tail
  have hEndTy :
      __smtx_typeof (__eo_to_smt rEnd) = SmtType.Seq T := by
    simpa [rEnd] using cprop_reverse_end_true_seq_type t s tc T hscTy hProg
  have hSfxTy :
      __smtx_typeof (__eo_to_smt rSfx) = SmtType.Seq T := by
    simpa [rSfx] using cprop_reverse_suffix_true_seq_type t s tc T htcTy hEndTy
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq rSfx T hSfxTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq rEnd nil T hEndTy hNilTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq rSfx tail T hSfxTy hTailTy
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hSfxNe : rSfx ≠ Term.Stuck := cprop_seq_type_ne_stuck rSfx T hSfxTy
  have hEndNe : rEnd ≠ Term.Stuck := cprop_seq_type_ne_stuck rEnd T hEndTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rEnd =
          Term.Apply (Term.UOp UserOp.str_concat) rEnd :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rEnd (by simp) hEndNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rEnd) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rSfx =
          Term.Apply (Term.UOp UserOp.str_concat) rSfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rSfx (by simp) hSfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rSfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean true) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_true, rSfx, rEnd, nil] using hEqGenEq
  rw [hFormulaEq]
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

private theorem step_concat_cprop_core
    (M : SmtModel) (hM : model_total_typed M)
    (rev t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    StepRuleProperties M
      [mkEq t s, mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))]
      (__eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ) := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck rev t s tc hProg with
    ⟨hProgEq, _hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htcTy]
        exact seq_ne_none T)
  rcases concatCProp_rev_cases_of_prog_ne_stuck rev t s tc hProg htcNe with
    hRev | hRev
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M
            (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true :=
        hPremisesTrue
          (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) (by simp)
      rcases cprop_context_true M hM t s tc hPremBool hNonzeroBool
          hProg hST with
        ⟨U, sc, tPrefix, sPrefix, tTail, sTail, hScEq, hRevIntroT,
          hRevIntroS, hTTailList, hSTailList, htcTy', hscTy, htPrefixTy,
          hsPrefixTy, hConcatEq⟩
      rw [hProgEq]
      exact facts_concat_cprop_true_formula M hM t s tc sc tPrefix sPrefix
        tTail sTail U hScEq hRevIntroT hRevIntroS hTTailList hSTailList
        htcTy' hscTy htPrefixTy hsPrefixTy hProg hNonzero hConcatEq
    · rw [hProgEq]
      exact concatCPropFormula_has_smt_translation_true t s tc hPremBool
        hNonzeroBool hProg hResultTy
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M
            (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true :=
        hPremisesTrue
          (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) (by simp)
      rcases cprop_context_false M hM t s tc hPremBool hNonzeroBool
          hProg hST with
        ⟨U, sc, tTail, sTail, hScEq, hIntroT, hIntroS, hTTailList,
          hSTailList, htcTy', hscTy, htTailTy, hsTailTy, hConcatEq⟩
      rw [hProgEq]
      exact facts_concat_cprop_false_formula M hM t s tc sc tTail sTail
        U hScEq hIntroT hIntroS hTTailList hSTailList htcTy' hscTy
        htTailTy hsTailTy hProg hNonzero hConcatEq
    · rw [hProgEq]
      exact concatCPropFormula_has_smt_translation_false t s tc hPremBool
        hNonzeroBool hProg hResultTy

theorem cmd_step_concat_cprop_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_cprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_cprop args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_cprop args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_cprop args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_cprop a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_cprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_cprop_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, u, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkNot (mkEq (mkStrLen u) (Term.Numeral 0)) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hNonzeroBool :
                          RuleProofs.eo_has_bool_type
                            (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_cprop a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_cprop a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkNot
                                    (mkEq (mkStrLen u) (Term.Numeral 0))))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_cprop a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_cprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_cprop_core M hM a1 lhs rhs u
                        hPremEqBool hNonzeroBool hProgRule hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
