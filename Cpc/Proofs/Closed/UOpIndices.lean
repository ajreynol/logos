import Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def native_eo_to_smt_uop_indices_safe : Term -> native_Bool
  | Term.Apply f x =>
    native_and (native_eo_to_smt_uop_indices_safe f) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp1 _ x =>
    native_and (native_eo_to_smt_closed x) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp2 _ x y =>
    native_and
      (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y))
      (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
  | Term.UOp3 _ x y z =>
    native_and
      (native_and (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y)) (native_eo_to_smt_closed z))
      (native_and
        (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
        (native_eo_to_smt_uop_indices_safe z))
  | _ => true

def NativeEoToSmtUOpIndicesSafe (x : Term) : Prop :=
  native_eo_to_smt_uop_indices_safe x = true

private theorem native_and_eq_true_intro {a b : native_Bool} :
    a = true ->
    b = true ->
    native_and a b = true := by
  intro ha hb
  cases a <;> cases b <;> simp [native_and] at ha hb ⊢

private theorem native_and_left_eq_true {a b : native_Bool} :
    native_and a b = true -> a = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_and_right_eq_true {a b : native_Bool} :
    native_and a b = true -> b = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_apply_intro
    {f x : Term}
    (hf : native_eo_to_smt_uop_indices_safe f = true)
    (hx : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hf, hx, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop1_intro
    {op : UserOp1} {x : Term}
    (hc : native_eo_to_smt_closed x = true)
    (hs : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hc, hs, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop2_intro
    {op : UserOp2} {x y : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hxs, hys,
    native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop3_intro
    {op : UserOp3} {x y z : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hzc : native_eo_to_smt_closed z = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true)
    (hzs : native_eo_to_smt_uop_indices_safe z = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp3 op x y z) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hzc, hxs, hys, hzs,
    native_and]

private theorem native_eo_to_smt_closed_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    native_eo_to_smt_closed x = true := by
  cases hx : native_eo_to_smt_closed x
  · exfalso
    apply h
    simp [native_eo_to_smt_guard_closed, native_ite, hx,
      TranslationProofs.smtx_typeof_none]
  · rfl

private theorem guard_body_type_non_none_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    __smtx_typeof body ≠ SmtType.None := by
  intro hBody
  cases hx : native_eo_to_smt_closed x
  · exact h (by
      simp [native_eo_to_smt_guard_closed, native_ite, hx,
        TranslationProofs.smtx_typeof_none])
  · exact h (by
      simpa [native_eo_to_smt_guard_closed, native_ite, hx] using hBody)

private theorem native_eo_to_smt_closed_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_closed x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid, native_eo_to_smt_closed,
    native_eo_to_smt_closed_rec] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_uop_indices_safe x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid,
    native_eo_to_smt_uop_indices_safe] at h ⊢

private theorem native_eo_to_smt_closed_rec_nil_of_closed
    {x : Term}
    (h : native_eo_to_smt_closed x = true) :
    native_eo_to_smt_closed_rec x [] = true := by
  simpa [native_eo_to_smt_closed] using h

private theorem native_eo_to_smt_closed_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_closed x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]

private theorem native_eo_to_smt_uop_indices_safe_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_uop_indices_safe]

private theorem smt_typeof_non_none_of_eq_non_none
    {x : Term} {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hNone
  exact hT (h.symm.trans hNone)

private theorem smtx_typeof_at_purify_arg_non_none
    {x : SmtTerm}
    (h : __smtx_typeof (SmtTerm._at_purify x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  intro hx
  exact h (by simpa [__smtx_typeof] using hx)

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid_rec :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T ->
      native_eo_to_smt_closed T = true ∧
        native_eo_to_smt_uop_indices_safe T = true
  | refs, Term.Bool, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.USort i, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.UOp op, h => by
      cases op <;> simp [eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | refs, Term.DatatypeType s d, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DatatypeTypeRef s, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hUc', hTs, hUs,
        native_and]
  | refs, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Set) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.Apply Term.FunType T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
          __smtx_type_wf
            (__eo_to_smt_type_tuple (__eo_to_smt_type T)
              (__eo_to_smt_type U)) = true) with ⟨hT, hU, _⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | Int =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Real =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Char =>
              exfalso
              simp [eo_type_valid_rec] at h
          | UnitTuple =>
              exfalso
              simp [eo_type_valid_rec] at h
          | BitVec =>
              cases x with
              | Numeral n =>
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | Set =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                ⟨hyc, hys⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                native_and]
          | UOp op =>
              cases op with
              | Array =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with
                    ⟨hy, hx⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | Tuple =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                          (__eo_to_smt_type x)) = true) with
                    ⟨hy, hx, _⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | _ =>
          exfalso
          simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_nil, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_cons, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Boolean b, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Numeral n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Rational q, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.String s, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Binary w n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Type, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Stuck, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.FunType, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Var name T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtCons s d i, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtSel s d i j, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UConst i T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UOp1 op x, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp2 op x y, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp3 op x y z, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid
    {T : Term} :
    eo_type_valid T ->
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  intro h
  cases T with
  | UOp op =>
      cases op <;> simp [eo_type_valid, eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | _ =>
      exact native_eo_to_smt_uop_indices_safe_of_type_valid_rec
        (refs := []) h

private theorem native_eo_to_smt_uop_indices_safe_of_smt_type_wf
    {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true :=
  native_eo_to_smt_uop_indices_safe_of_type_valid
    (eo_type_valid_of_smt_wf T hWf)

private theorem native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Seq A =>
    have hSeqNN : __smtx_typeof (SmtTerm.seq_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_seq_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSeqNN
      exact hSeqNN
    have hWfSeq :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Seq A) (SmtType.Seq A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSeq
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_seq_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_set_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Set A =>
    have hSetNN : __smtx_typeof (SmtTerm.set_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_set_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Set A) (SmtType.Set A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSetNN
      exact hSetNN
    have hWfSet :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Set A) (SmtType.Set A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSet
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_set_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_uop1_non_none
    {op : UserOp1} {x : Term}
    (ih :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp1 op x)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  cases op
  case _at_purify =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smtx_typeof_at_purify_arg_non_none hBody
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case seq_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  case _at_strings_stoi_non_digit =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof
            (SmtTerm.str_indexof_re (__eo_to_smt x)
              (SmtTerm.re_comp
                (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                  (SmtTerm.String (native_string_lit "9"))))
              (SmtTerm.Numeral 0)) ≠ SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hArgs :=
      str_indexof_re_args_of_non_none
        (t1 := __eo_to_smt x)
        (t2 :=
          SmtTerm.re_comp
            (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
        (t3 := SmtTerm.Numeral 0) hBody
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case set_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_set_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  all_goals
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

/--
If a term translates to a well-typed SMT term, then every indexed EO operator
occurrence in it has standalone-closed immediate indices.

The guarded branches in `__eo_to_smt` should discharge the opaque term-index
cases; the numeric-index branches are intended to be discharged from the SMT
typing rules that require their indices to translate to `SmtTerm.Numeral`.
-/
theorem eo_to_smt_well_typed_implies_uop_indices_safe
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    NativeEoToSmtUOpIndicesSafe t := by
  let rec go : (u : Term) ->
      __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
      NativeEoToSmtUOpIndicesSafe u
    | u, h => by
        cases u <;>
          simp [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] at h ⊢
        case UOp1 op x =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop1_non_none
              (x := x) (op := op) (fun hx => go x hx) h
        all_goals
          sorry
  exact go t
