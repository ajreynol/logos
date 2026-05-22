import Cpc.Proofs.RuleSupport.RegexSupport
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private def nativeSigmaPrefix : Nat -> native_RegLan
  | 0 => SmtRegLan.epsilon
  | 1 => native_re_allchar
  | n + 2 => SmtRegLan.concat native_re_allchar (nativeSigmaPrefix (n + 1))

private theorem nativeSigmaPrefix_succ_ne_empty (n : Nat) :
    nativeSigmaPrefix (n + 1) ≠ SmtRegLan.empty := by
  cases n <;> simp [nativeSigmaPrefix, native_re_allchar]

private theorem nativeSigmaPrefix_succ_ne_epsilon (n : Nat) :
    nativeSigmaPrefix (n + 1) ≠ SmtRegLan.epsilon := by
  cases n <;> simp [nativeSigmaPrefix, native_re_allchar]

private theorem nativeListInRe_sigmaPrefix_cons
    (c : Char) (cs : List Char) (n : Nat) :
    nativeListInRe (c :: cs) (nativeSigmaPrefix (n + 1)) =
      nativeListInRe cs (nativeSigmaPrefix n) := by
  cases n with
  | zero =>
      simp [nativeSigmaPrefix, nativeListInRe, native_re_deriv, native_re_allchar]
  | succ n =>
      change
        nativeListInRe cs
            (native_re_mk_union
              (native_re_mk_concat SmtRegLan.epsilon (nativeSigmaPrefix (n + 1)))
              SmtRegLan.empty) =
          nativeListInRe cs (nativeSigmaPrefix (n + 1))
      rw [nativeListInRe_mk_union, nativeListInRe_mk_concat_epsilon_left,
        nativeListInRe_empty]
      simp

private theorem nativeListInRe_sigmaPrefix_true_iff :
    (n : Nat) -> (xs : List Char) ->
      nativeListInRe xs (nativeSigmaPrefix n) = true <-> xs.length = n
  | 0, xs => by
      cases xs with
      | nil =>
          simp [nativeSigmaPrefix, nativeListInRe, native_re_nullable]
      | cons c cs =>
          simpa [nativeSigmaPrefix, nativeListInRe, native_re_nullable,
            native_re_deriv] using nativeListInRe_empty cs
  | n + 1, xs => by
      constructor
      · intro h
        cases xs with
        | nil =>
            cases n <;>
              simp [nativeSigmaPrefix, nativeListInRe, native_re_nullable,
                native_re_allchar] at h
        | cons c cs =>
            have hTail :
                nativeListInRe cs (nativeSigmaPrefix n) = true := by
              simpa [nativeListInRe_sigmaPrefix_cons c cs n] using h
            have hTailLen :=
              (nativeListInRe_sigmaPrefix_true_iff n cs).1 hTail
            simp [hTailLen]
      · intro hLen
        cases xs with
        | nil =>
            simp at hLen
        | cons c cs =>
            have hTailLen : cs.length = n := by
              simp at hLen
              omega
            have hTail :
                nativeListInRe cs (nativeSigmaPrefix n) = true :=
              (nativeListInRe_sigmaPrefix_true_iff n cs).2 hTailLen
            simpa [nativeListInRe_sigmaPrefix_cons c cs n] using hTail

private theorem nativeListInRe_sigmaPrefixStar_nil (n : Nat) :
    nativeListInRe [] (native_re_mult (nativeSigmaPrefix n)) = true := by
  generalize hr : nativeSigmaPrefix n = r
  cases r <;> simp [native_re_mult, native_re_mk_star, nativeListInRe,
    native_re_nullable]

private theorem nativeListInRe_sigmaPrefixStar_cons
    (c : Char) (cs : List Char) (n : Nat) :
    nativeListInRe (c :: cs)
        (native_re_mult (nativeSigmaPrefix (n + 1))) =
      nativeListInRe cs
        (native_re_mk_concat (nativeSigmaPrefix n)
          (native_re_mult (nativeSigmaPrefix (n + 1)))) := by
  cases n with
  | zero =>
      simp [nativeListInRe, native_re_mult, native_re_mk_star, nativeSigmaPrefix,
        native_re_deriv, native_re_mk_concat, native_re_allchar]
  | succ n =>
      change
        nativeListInRe cs
            (native_re_mk_concat
              (native_re_mk_union
                (native_re_mk_concat SmtRegLan.epsilon (nativeSigmaPrefix (n + 1)))
                SmtRegLan.empty)
              (native_re_mult (nativeSigmaPrefix (n + 2)))) =
          nativeListInRe cs
            (native_re_mk_concat (nativeSigmaPrefix (n + 1))
              (native_re_mult (nativeSigmaPrefix (n + 2))))
      apply nativeListInRe_mk_concat_congr
      · intro ys
        rw [nativeListInRe_mk_union, nativeListInRe_mk_concat_epsilon_left,
          nativeListInRe_empty]
        simp
      · intro ys
        rfl

private theorem nativeListInRe_sigmaPrefixStar_true_iff_dvd
    (n : Nat) (hn : n ≠ 0) (xs : List Char) :
    nativeListInRe xs (native_re_mult (nativeSigmaPrefix n)) = true <->
      n ∣ xs.length := by
  cases n with
  | zero =>
      exact False.elim (hn rfl)
  | succ k =>
      let step := k + 1
      have hstep : step ≠ 0 := by omega
      have hMain :
          forall xs : List Char,
            nativeListInRe xs (native_re_mult (nativeSigmaPrefix step)) = true <->
              step ∣ xs.length := by
        have hByLen :
            forall l : Nat, forall ys : List Char, ys.length = l ->
              (nativeListInRe ys (native_re_mult (nativeSigmaPrefix step)) = true <->
                step ∣ ys.length) := by
          intro l
          refine Nat.strongRecOn l (motive := fun l =>
            forall ys : List Char, ys.length = l ->
              (nativeListInRe ys (native_re_mult (nativeSigmaPrefix step)) = true <->
                step ∣ ys.length)) ?_
          intro l ih ys hLen
          cases ys with
          | nil =>
              constructor
              · intro _; exact Nat.dvd_zero step
              · intro _; exact nativeListInRe_sigmaPrefixStar_nil step
          | cons c cs =>
              constructor
              · intro h
                rw [nativeListInRe_sigmaPrefixStar_cons c cs k] at h
                rcases (nativeListInRe_mk_concat_true_iff_exists_append cs
                    (nativeSigmaPrefix k)
                    (native_re_mult (nativeSigmaPrefix step))).1 h with
                  ⟨ys, zs, hAppend, hYs, hZs⟩
                have hYsLen : ys.length = k :=
                  (nativeListInRe_sigmaPrefix_true_iff k ys).1 hYs
                have hAppendLen := congrArg List.length hAppend
                have hZsLt : zs.length < l := by
                  simp [hYsLen] at hAppendLen
                  simp at hLen
                  omega
                have hZsDvd : step ∣ zs.length :=
                  (ih zs.length hZsLt zs rfl).1 hZs
                rcases hZsDvd with ⟨q, hq⟩
                have hCsLen : cs.length = k + zs.length := by
                  simp [hYsLen] at hAppendLen
                  omega
                refine ⟨q + 1, ?_⟩
                calc
                  (c :: cs).length = k + zs.length + 1 := by
                    simp [hCsLen]
                  _ = k + step * q + 1 := by
                    rw [hq]
                  _ = step * (q + 1) := by
                    rw [Nat.mul_succ]
                    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              · intro hDvd
                rw [nativeListInRe_sigmaPrefixStar_cons c cs k]
                rcases hDvd with ⟨q, hq⟩
                cases q with
                | zero =>
                    simp [step] at hq
                | succ q =>
                    have hqCons : (c :: cs).length = step * q + step := by
                      simpa [Nat.mul_succ] using hq
                    have hCsLen : cs.length = k + step * q := by
                      have hqLen : cs.length + 1 = step * q + step := by
                        simpa using hqCons
                      have hstepEq : step = k + 1 := rfl
                      omega
                    let ys := cs.take k
                    let zs := cs.drop k
                    have hYsLen : ys.length = k := by
                      rw [List.length_take]
                      exact Nat.min_eq_left (by omega)
                    have hZsLen : zs.length = step * q := by
                      simp [ys, zs, hCsLen]
                    have hZsLt : zs.length < l := by
                      have hLen' : l = step * q + step := by
                        rw [← hLen]
                        exact hqCons
                      have hstepPos : 0 < step := by omega
                      rw [hZsLen]
                      omega
                    have hZsDvd : step ∣ zs.length := by
                      refine ⟨q, ?_⟩
                      exact hZsLen
                    have hZsMem :
                        nativeListInRe zs
                            (native_re_mult (nativeSigmaPrefix step)) = true :=
                      (ih zs.length hZsLt zs rfl).2 hZsDvd
                    exact (nativeListInRe_mk_concat_true_iff_exists_append cs
                      (nativeSigmaPrefix k)
                      (native_re_mult (nativeSigmaPrefix step))).2
                      ⟨ys, zs, by simp [ys, zs],
                        (nativeListInRe_sigmaPrefix_true_iff k ys).2 hYsLen,
                        hZsMem⟩
        intro xs
        exact hByLen xs.length xs rfl
      simpa [step] using hMain xs

private theorem nativeListInRe_sigmaPrefixStar_eq_int_mod
    (n : Nat) (hn : n ≠ 0) (xs : List Char) :
    nativeListInRe xs (native_re_mult (nativeSigmaPrefix n)) =
      decide (((xs.length : Int) % (Int.ofNat n)) = 0) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_iff]
    have hDvdNat : n ∣ xs.length :=
      (nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn xs).1 h
    have hDvdInt : (Int.ofNat n) ∣ (Int.ofNat xs.length) := by
      rcases hDvdNat with ⟨q, hq⟩
      refine ⟨Int.ofNat q, ?_⟩
      rw [hq]
      simp
    exact Int.emod_eq_zero_of_dvd hDvdInt
  · intro h
    have hMod : ((xs.length : Int) % (Int.ofNat n)) = 0 :=
      of_decide_eq_true h
    have hDvdInt : (Int.ofNat n) ∣ (Int.ofNat xs.length) :=
      Int.dvd_of_emod_eq_zero hMod
    have hDvdNat : n ∣ xs.length := by
      rw [<- Int.ofNat_dvd]
      exact hDvdInt
    exact (nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn xs).2 hDvdNat

private theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).toList.length = (native_unpack_seq ss).length := by
  simp [native_unpack_string, native_ssm_string_of_char_values]

private theorem native_unpack_string_strlen_eq (ss : SmtSeq) :
    String.length (native_unpack_string ss) = (native_unpack_seq ss).length := by
  simpa using native_unpack_string_length_eq ss

private theorem str_in_re_sigma_star_rec_empty_ne_zero
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String ""))
        (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      n ≠ 0 := by
  intro hSide hn
  apply hSide
  subst n
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      simp [__str_mk_str_in_re_sigma_star_rec, __eo_requires, __eo_eq,
        native_teq, native_ite, native_not, SmtEval.native_not]

private theorem str_in_re_sigma_star_rec_empty_eq
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) (hn : n ≠ 0) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String ""))
        (Term.Numeral (Int.ofNat n)) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.mod)
              (Term.Apply (Term.UOp UserOp.str_len) s))
            (Term.Numeral (Int.ofNat n))))
        (Term.Numeral 0) := by
  have hnInt : (Int.ofNat n) ≠ 0 := by
    intro hZero
    exact hn (Int.ofNat_eq_zero.mp hZero)
  have hZeroNe : (0 : Int) ≠ Int.ofNat n := by
    intro hZero
    exact hn (Int.ofNat_eq_zero.mp hZero.symm)
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      (simp [__str_mk_str_in_re_sigma_star_rec, __eo_requires, __eo_eq,
        native_teq, native_ite, native_not, hnInt, hZeroNe, SmtEval.native_not]
       exact hZeroNe)

private theorem str_in_re_sigma_star_rec_str_to_re_nonempty_eq_stuck
    (s : Term) (str : native_String) (n : Nat)
    (hStr : str ≠ "") :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String str))
        (Term.Numeral (Int.ofNat n)) =
      Term.Stuck := by
  cases s <;> unfold __str_mk_str_in_re_sigma_star_rec <;> simp [hStr]

private theorem str_in_re_sigma_star_rec_allchar_eq
    (s r : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_allchar)) r)
        (Term.Numeral (Int.ofNat n)) =
      __str_mk_str_in_re_sigma_star_rec s r
        (Term.Numeral (Int.ofNat (n + 1))) := by
  simp [__str_mk_str_in_re_sigma_star_rec, __eo_add, native_zplus, Int.natCast_add]

private theorem smtx_model_eval_str_in_re_sigma_star_rec
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (r : Term) (rv : native_RegLan) (n : Nat) :
      __str_mk_str_in_re_sigma_star_rec s r
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      exists m : Nat,
        rv = nativeSigmaPrefix m /\
          n + m ≠ 0 /\
          __smtx_model_eval M
              (__eo_to_smt
                (__str_mk_str_in_re_sigma_star_rec s r
                  (Term.Numeral (Int.ofNat n)))) =
            SmtValue.Boolean
              (decide ((((native_unpack_string ss).toList.length : Int) %
                (Int.ofNat (n + m))) = 0))
:= by
  intro hSide hREval
  cases r with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases x with
              | String str =>
                  by_cases hStr : str = ""
                  · subst str
                    have hRv : rv = SmtRegLan.epsilon := by
                      change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String "")) =
                          SmtValue.RegLan rv at hREval
                      rw [__smtx_model_eval.eq_106, __smtx_model_eval.eq_4] at hREval
                      simpa [__smtx_model_eval_str_to_re, native_str_to_re,
                        native_unpack_string, native_pack_string, native_pack_seq,
                        native_unpack_seq, native_ssm_char_values_of_string,
                        native_ssm_string_of_char_values, native_re_of_list] using hREval.symm
                    subst rv
                    have hn : n ≠ 0 :=
                      str_in_re_sigma_star_rec_empty_ne_zero s n hSNe hSide
                    refine ⟨0, by simp [nativeSigmaPrefix], by simpa using hn, ?_⟩
                    rw [str_in_re_sigma_star_rec_empty_eq s n hSNe hn]
                    change
                      __smtx_model_eval M
                          (SmtTerm.eq
                            (SmtTerm.mod (SmtTerm.str_len (__eo_to_smt s))
                              (SmtTerm.Numeral (Int.ofNat n)))
                            (SmtTerm.Numeral 0)) =
                        SmtValue.Boolean
                          (decide ((((native_unpack_string ss).toList.length : Int) %
                            (Int.ofNat (n + 0))) = 0))
                    rw [__smtx_model_eval.eq_134, __smtx_model_eval.eq_25,
                      __smtx_model_eval.eq_79, __smtx_model_eval.eq_2,
                      __smtx_model_eval.eq_2, hSEval]
                    have hnInt : (Int.ofNat n) ≠ 0 := by
                      intro hZero
                      exact hn (Int.ofNat_eq_zero.mp hZero)
                    simp [__smtx_model_eval_eq, __smtx_model_eval_mod_total,
                      __smtx_model_eval_str_len, __smtx_model_eval_ite,
                      native_veq, native_zeq, native_mod_total, hnInt,
                      native_seq_len, native_unpack_string_length_eq,
                      native_unpack_string_strlen_eq, hn]
                  · exfalso
                    apply hSide
                    exact str_in_re_sigma_star_rec_str_to_re_nonempty_eq_stuck
                      s str n hStr
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_star_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_star_rec]
      | Apply f1 y =>
          cases f1 with
          | UOp op1 =>
              cases op1 with
              | re_concat =>
                  cases y with
                  | UOp yop =>
                      cases yop with
                      | re_allchar =>
                          change __smtx_model_eval M
                              (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt x)) =
                            SmtValue.RegLan rv at hREval
                          rw [__smtx_model_eval.eq_113, __smtx_model_eval.eq_103] at hREval
                          cases hTailEval : __smtx_model_eval M (__eo_to_smt x) with
                          | RegLan rvTail =>
                              have hRv : rv = native_re_concat native_re_allchar rvTail := by
                                simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                                exact hREval.symm
                              subst rv
                              have hSideTail :
                                  __str_mk_str_in_re_sigma_star_rec s x
                                      (Term.Numeral (Int.ofNat (n + 1))) ≠
                                    Term.Stuck := by
                                rw [<- str_in_re_sigma_star_rec_allchar_eq s x n hSNe]
                                exact hSide
                              rcases smtx_model_eval_str_in_re_sigma_star_rec
                                  M s ss hSNe hSEval x rvTail (n + 1)
                                  hSideTail hTailEval with
                                ⟨m, hTailRv, hTotalNe, hEval⟩
                              refine ⟨m + 1, ?_, ?_, ?_⟩
                              · subst rvTail
                                cases m with
                                | zero =>
                                    simp [native_re_concat, nativeSigmaPrefix,
                                      native_re_mk_concat, native_re_allchar]
                                | succ m =>
                                    have hNeEmpty := nativeSigmaPrefix_succ_ne_empty m
                                    have hNeEps := nativeSigmaPrefix_succ_ne_epsilon m
                                    simp [native_re_concat, nativeSigmaPrefix,
                                      native_re_mk_concat, native_re_allchar,
                                      hNeEmpty, hNeEps]
                              · omega
                              · rw [str_in_re_sigma_star_rec_allchar_eq s x n hSNe]
                                have hTotal :
                                    n + (m + 1) = n + 1 + m := by
                                  omega
                                simpa [hTotal] using hEval
                          | _ =>
                              simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                      | _ =>
                          exfalso
                          apply hSide
                          simpa [__str_mk_str_in_re_sigma_star_rec]
                  | _ =>
                      exfalso
                      apply hSide
                      simpa [__str_mk_str_in_re_sigma_star_rec]
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_star_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_star_rec]
      | _ =>
          exfalso
          apply hSide
          simpa [__str_mk_str_in_re_sigma_star_rec]
  | _ =>
      exfalso
      apply hSide
      simpa [__str_mk_str_in_re_sigma_star_rec]
termination_by r

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  have hxNe : y ≠ Term.Stuck := by
    intro hy
    subst y
    simp [native_not] at hxOk
  exact hxNe hx

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) /\
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x /\
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_in_re_args_smt_types_of_has_translation
    (s r : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char /\
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) ≠
      SmtType.None
    exact hTrans
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re) (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

private theorem smtx_model_eval_str_in_re_eq_sigma_star_side
    (M : SmtModel) (s r side : Term) (ss : SmtSeq) (rv : native_RegLan)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      side = __str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0))
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply (Term.UOp UserOp.re_mult) r))) =
      __smtx_model_eval M (__eo_to_smt side) := by
  subst side
  rcases smtx_model_eval_str_in_re_sigma_star_rec M s ss hSNe hSEval r rv 0
      hSideNe hREval with
    ⟨m, hRv, hMNe, hSideEval⟩
  have hSideEval' :
      __smtx_model_eval M
          (__eo_to_smt (__str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0))) =
        SmtValue.Boolean
          (decide ((((native_unpack_string ss).toList.length : Int) %
            (Int.ofNat (0 + m))) = 0)) := by
    simpa using hSideEval
  rw [hSideEval']
  change
    __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (SmtTerm.re_mult (__eo_to_smt r))) =
      SmtValue.Boolean
        (decide ((((native_unpack_string ss).toList.length : Int) %
          (Int.ofNat (0 + m))) = 0))
  rw [__smtx_model_eval.eq_118, __smtx_model_eval.eq_107]
  rw [hSEval, hREval]
  subst rv
  have hm : m ≠ 0 := by
    simpa using hMNe
  simp only [__smtx_model_eval_re_mult, __smtx_model_eval_str_in_re]
  change
    SmtValue.Boolean
        (nativeListInRe (native_unpack_string ss).toList
          (native_re_mult (nativeSigmaPrefix m))) =
      SmtValue.Boolean
        (decide ((((native_unpack_string ss).toList.length : Int) %
          (Int.ofNat (0 + m))) = 0))
  rw [nativeListInRe_sigmaPrefixStar_eq_int_mod m hm]
  simp

private theorem str_in_re_sigma_star_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b))
    (hProgNe :
      __eo_prog_str_in_re_sigma_star
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_sigma_star
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b)) := by
  let reStar := Term.Apply (Term.UOp UserOp.re_mult) r
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) reStar
  let side := __str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0)
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hReqEq : side = b := eo_requires_eq_of_ne_stuck side b body hProgNe
  have hReqResult : __eo_requires side b body = body :=
    eo_requires_result_eq_of_ne_stuck side b body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hProgNe
  subst b
  change StepRuleProperties M [] (__eo_requires side side body)
  rw [hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [reStar, strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn side hEqTrans with
    ⟨hStrInTrans, _hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s reStar (by
      simpa [strIn] using hStrInTrans) with
    ⟨hSTy, hStarTy⟩
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    have hRNN : term_has_non_none_type (__eo_to_smt r) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hStarTy
      rw [typeof_re_mult_eq] at hStarTy
      by_cases hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
      · rw [hRTy]
        simp
      · simp [hRTy, native_ite, native_Teq] at hStarTy
    have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hStarTy
      rw [typeof_re_mult_eq] at hStarTy
      by_cases hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
      · exact hRTy
      · simp [hRTy, native_ite, native_Teq] at hStarTy
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) hRNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSNe : s ≠ Term.Stuck := by
    intro hs
    apply hSideNe
    subst s
    simp [side, __str_mk_str_in_re_sigma_star_rec]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt strIn) =
        __smtx_model_eval M (__eo_to_smt side) := by
    exact smtx_model_eval_str_in_re_eq_sigma_star_side M s r side ss rv hSNe hSEval
      hREval rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt side))

end RuleProofs

theorem cmd_step_str_in_re_sigma_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_sigma_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises ≠ Term.Stuck :=
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp reStar =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              cases reStar with
                                              | Apply starOp r =>
                                                  cases starOp with
                                                  | UOp starOpName =>
                                                      cases starOpName with
                                                      | re_mult =>
                                                          have hProps :=
                                                            RuleProofs.str_in_re_sigma_star_valid_properties
                                                              M hM str r b (by
                                                                simpa using hA1Trans) (by
                                                                change
                                                                  __eo_prog_str_in_re_sigma_star
                                                                    (Term.Apply
                                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                                        (Term.Apply
                                                                          (Term.Apply
                                                                            (Term.UOp UserOp.str_in_re) str)
                                                                          (Term.Apply
                                                                            (Term.UOp UserOp.re_mult) r))) b) ≠
                                                                    Term.Stuck at hProg
                                                                exact hProg)
                                                          change StepRuleProperties M []
                                                            (__eo_prog_str_in_re_sigma_star
                                                              (Term.Apply
                                                                (Term.Apply (Term.UOp UserOp.eq)
                                                                  (Term.Apply
                                                                    (Term.Apply
                                                                      (Term.UOp UserOp.str_in_re) str)
                                                                    (Term.Apply
                                                                      (Term.UOp UserOp.re_mult) r))) b))
                                                          simpa [premiseTermList] using hProps
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
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
