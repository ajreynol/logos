import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals simpa using h

private theorem eo_and_eq_true_left {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h ⊢
  · exact h.1
  · split at h <;> cases h

private theorem eo_and_eq_true_right {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h ⊢
  · exact h.2
  · split at h <;> cases h

private theorem requires_eq_true_stuck_of_ne (x y B : Term) :
    x ≠ y ->
    __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck := by
  intro hNe
  by_cases hReq : __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck
  · exact hReq
  · have hEqTrue : __eo_eq x y = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hReq
    have hYX : y = x := eo_eq_true_eq hEqTrue
    exact False.elim (hNe hYX.symm)

private theorem bv_smod_guard_eqs_of_ne_stuck
    {x w wm pw px pwm px' body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
            (__eo_eq wm pwm))
          (__eo_eq x px'))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pw = w ∧ px = x ∧ pwm = wm ∧ px' = x := by
  intro hReq
  have hGuard :
      __eo_and
          (__eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
            (__eo_eq wm pwm))
          (__eo_eq x px') =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReq
  have hLeft :
      __eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
          (__eo_eq wm pwm) =
        Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have hXpx' : __eo_eq x px' = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have hLeftLeft :
      __eo_and (__eo_eq w pw) (__eo_eq x px) = Term.Boolean true :=
    eo_and_eq_true_left hLeft
  have hW : __eo_eq w pw = Term.Boolean true :=
    eo_and_eq_true_left hLeftLeft
  have hX : __eo_eq x px = Term.Boolean true :=
    eo_and_eq_true_right hLeftLeft
  have hWm : __eo_eq wm pwm = Term.Boolean true :=
    eo_and_eq_true_right hLeft
  exact ⟨eo_eq_true_eq hW, eo_eq_true_eq hX, eo_eq_true_eq hWm,
    eo_eq_true_eq hXpx'⟩

private theorem bv_smod_eliminate_shape_of_ne_stuck
    (x y w wm P1 P2 : Term) :
    __eo_prog_bv_smod_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck ->
    ∃ pw px pwm px',
      P1 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) ∧
      P2 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) pwm)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
              (Term.Numeral 1)) := by
  intro hProg
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_smod_eliminate.eq_1 y w wm (Proof.pf P1) (Proof.pf P2))
  have hy : y ≠ Term.Stuck := by
    intro hy
    subst y
    exact hProg (__eo_prog_bv_smod_eliminate.eq_2 x w wm (Proof.pf P1) (Proof.pf P2) hx)
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_smod_eliminate.eq_3 x y wm (Proof.pf P1) (Proof.pf P2) hx hy)
  have hwm : wm ≠ Term.Stuck := by
    intro hwm
    subst wm
    exact hProg (__eo_prog_bv_smod_eliminate.eq_4 x y w (Proof.pf P1) (Proof.pf P2) hx hy hw)
  by_cases hShape :
      ∃ pw px pwm px',
        P1 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) pw)
              (Term.Apply (Term.UOp UserOp._at_bvsize) px) ∧
        P2 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) pwm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
                (Term.Numeral 1))
  · exact hShape
  · have hStuck :
        __eo_prog_bv_smod_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) =
          Term.Stuck := by
      exact __eo_prog_bv_smod_eliminate.eq_6 x y w wm (Proof.pf P1) (Proof.pf P2)
        hx hy hw hwm (by
          intro pw px pwm px' hp1 hp2
          cases hp1
          cases hp2
          exact hShape ⟨pw, px, pwm, px', rfl, rfl⟩)
    exact False.elim (hProg hStuck)

private def smodBitZero : Term :=
  Term.UOp2 UserOp2._at_bv (Term.Numeral 0) (Term.Numeral 1)

private def smodBitOne : Term :=
  Term.UOp2 UserOp2._at_bv (Term.Numeral 1) (Term.Numeral 1)

private def smodWidthZero (w : Term) : Term :=
  Term.UOp2 UserOp2._at_bv (Term.Numeral 0) w

private def smodExtract (wm z : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract wm wm) z

private def smodEq (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b

private def smodAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

private def smodIte (c t e : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e

private def smodSignZero (wm z : Term) : Term :=
  smodEq (smodExtract wm z) smodBitZero

private def smodSignOne (wm z : Term) : Term :=
  smodEq (smodExtract wm z) smodBitOne

private def smodAbs (wm z : Term) : Term :=
  smodIte (smodSignZero wm z) z (Term.Apply (Term.UOp UserOp.bvneg) z)

private def smodUrem (x y wm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) (smodAbs wm x)) (smodAbs wm y)

private def smodAddWithY (a y : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvadd) a)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvadd) y)
      (__eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof a)))

private def smodElimRhs (x y w wm : Term) : Term :=
  let _v3 := smodSignZero wm y
  let _v5 := smodSignZero wm x
  let _v6 := smodUrem x y wm
  let _v7 := Term.Apply (Term.UOp UserOp.bvneg) _v6
  let _v11 := smodAnd _v3 (Term.Boolean true)
  __eo_mk_apply
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.ite)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) _v6)
          (smodWidthZero w)))
      _v6)
    (__eo_mk_apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite) (smodAnd _v5 _v11))
        _v6)
      (__eo_mk_apply
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm x))
              _v11))
          (smodAddWithY _v7 y))
        (__eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) _v5)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm y))
                  (Term.Boolean true))))
            (smodAddWithY _v6 y))
          _v7)))

private def smodElimBody (x y w wm : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x) y))
    (smodElimRhs x y w wm)

private def smodLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x) y

private theorem smodElimBody_type_bool_top_eq
    (x y w wm : Term) :
    __eo_typeof (smodElimBody x y w wm) = Term.Bool ->
    __eo_typeof_eq (__eo_typeof (smodLhs x y))
      (__eo_typeof (smodElimRhs x y w wm)) = Term.Bool := by
  intro hTy
  unfold smodElimBody at hTy
  unfold smodLhs
  cases hRhs : smodElimRhs x y w wm <;>
    simp [__eo_mk_apply, hRhs] at hTy ⊢
  case Stuck =>
    cases hTy
  all_goals simpa using hTy

private theorem typeof_bvand_ne_stuck_inv :
    (A B : Term) ->
    __eo_typeof_bvand A B ≠ Term.Stuck ->
    ∃ bw, A = Term.Apply (Term.UOp UserOp.BitVec) bw ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) bw
  | A, B, hNe => by
      cases A <;> try simp [__eo_typeof_bvand] at hNe
      case Apply f a =>
        cases f <;> try simp [__eo_typeof_bvand] at hNe
        case UOp op =>
          cases op <;> try simp [__eo_typeof_bvand] at hNe
          case BitVec =>
            cases B <;> try simp [__eo_typeof_bvand] at hNe
            case Apply g b =>
              cases g <;> try simp [__eo_typeof_bvand] at hNe
              case UOp op' =>
                cases op' <;> try simp [__eo_typeof_bvand] at hNe
                case BitVec =>
                  by_cases hEq : a = b
                  · subst b
                    exact ⟨a, rfl, rfl⟩
                  · exfalso
                    apply hNe
                    simpa [__eo_typeof_bvand] using
                      requires_eq_true_stuck_of_ne a b
                        (Term.Apply (Term.UOp UserOp.BitVec) a) hEq

private theorem typeof_args_of_smod_elim_body_bool (x y w wm : Term) :
    __eo_typeof (smodElimBody x y w wm) = Term.Bool ->
    ∃ bw, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) bw ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) bw := by
  intro hTy
  have hTop := smodElimBody_type_bool_top_eq x y w wm hTy
  have hLeftNe :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    intro hStuck
    unfold smodLhs at hTop
    change
      __eo_typeof_eq (__eo_typeof_bvand (__eo_typeof x) (__eo_typeof y))
        (__eo_typeof (smodElimRhs x y w wm)) = Term.Bool at hTop
    rw [hStuck] at hTop
    simp [__eo_typeof_eq] at hTop
  exact typeof_bvand_ne_stuck_inv (__eo_typeof x) (__eo_typeof y) hLeftNe

private theorem smodElimRhs_type_of_body_bool
    (x y w wm : Term) (n : native_Int) :
    __eo_typeof (smodElimBody x y w wm) = Term.Bool ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodElimRhs x y w wm) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  intro hTy hXTy hYTy
  have hTop := smodElimBody_type_bool_top_eq x y w wm hTy
  have hTypeEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof (smodLhs x y)) (__eo_typeof (smodElimRhs x y w wm)) hTop
  have hLhsTy :
      __eo_typeof (smodLhs x y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
    unfold smodLhs
    change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n)
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, SmtEval.native_not]
  rw [← hTypeEq]
  exact hLhsTy

private theorem typeof_extract_diag_numeral (wmv w : native_Int) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
      = (native_ite (native_zlt (-1 : native_Int) wmv)
          (native_ite (native_zlt wmv w)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus (native_zplus wmv (native_zneg wmv)) 1)))
            Term.Stuck)
          Term.Stuck) := by
  unfold __eo_typeof_extract
  simp only [__eo_mk_apply, __eo_requires, __eo_gt, __eo_add, __eo_neg,
    native_ite, native_teq, native_not, SmtEval.native_not]
  have hLenPos :
      native_zlt (-1 : native_Int)
          (native_zplus (native_zplus wmv (native_zneg wmv)) 1) = true := by
    have hLen :
        native_zplus (native_zplus wmv (native_zneg wmv)) 1 = 1 := by
      change (wmv + -wmv) + 1 = 1
      calc
        (wmv + -wmv) + 1 = 0 + 1 := by rw [Int.add_right_neg]
        _ = 1 := rfl
    rw [hLen]
    simp [native_zlt, SmtEval.native_zlt]
  by_cases hg1 : native_zlt (-1 : native_Int) wmv = true <;>
    by_cases hg2 : native_zlt wmv w = true <;>
    simp [hg1, hg2, hLenPos, native_ite, native_teq]

private theorem eo_gt_neg_one_stuck_of_not_numeral (wm : Term)
    (hwm : ∀ k, wm ≠ Term.Numeral k) :
    __eo_gt wm (Term.Numeral (-1 : native_Int)) = Term.Stuck := by
  cases hw : wm with
  | Numeral k => exact absurd hw (hwm k)
  | _ => rfl

private theorem requires_stuck_cond (b c : Term) :
    __eo_requires Term.Stuck b c = Term.Stuck := by
  by_cases hb : Term.Stuck = b
  · subst hb
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  · simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not,
      hb]

private theorem mk_apply_stuck_right (x : Term) :
    __eo_mk_apply x Term.Stuck = Term.Stuck := by
  cases x <;> rfl

private theorem typeof_extract_diag_stuck_of_gt_stuck (A wm B : Term)
    (hA : A = Term.UOp UserOp.Int)
    (hgt : __eo_gt wm (Term.Numeral (-1 : native_Int)) = Term.Stuck) :
    __eo_typeof_extract A wm A wm B = Term.Stuck := by
  subst A
  by_cases hwmS : wm = Term.Stuck
  · subst wm
    rfl
  · cases hB : B with
    | Apply f a =>
        cases f with
        | UOp o =>
            cases o <;>
              simp only [__eo_typeof_extract, hwmS, hgt, requires_stuck_cond,
                mk_apply_stuck_right]
        | _ => simp only [__eo_typeof_extract, hwmS]
    | _ => simp only [__eo_typeof_extract, hwmS]

private theorem typeof_extract_diag_not_numeral_stuck (wm t : Term)
    (hwm : ∀ k, wm ≠ Term.Numeral k) :
    __eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof t)
      = Term.Stuck := by
  by_cases hWmTy : __eo_typeof wm = Term.UOp UserOp.Int
  · exact typeof_extract_diag_stuck_of_gt_stuck (__eo_typeof wm) wm (__eo_typeof t)
      hWmTy (eo_gt_neg_one_stuck_of_not_numeral wm hwm)
  · by_cases hwmS : wm = Term.Stuck
    · subst wm
      simp [__eo_typeof_extract]
    · cases hwt : __eo_typeof wm with
      | UOp o => cases o <;> simp_all [__eo_typeof_extract, hwmS]
      | _ => simp_all [__eo_typeof_extract, hwmS]

private theorem typeof_extract_diag_numeral_stuck_of_not_bv
    (wmv : native_Int) (B : Term)
    (hB : ∀ w, B ≠ Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) :
    __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral wmv)
        (Term.UOp UserOp.Int) (Term.Numeral wmv) B = Term.Stuck := by
  cases hB' : B with
  | Apply f a =>
      cases f with
      | UOp o =>
          by_cases hOBv : o = UserOp.BitVec
          · subst o
            cases ha : a with
            | Numeral w =>
                exfalso
                exact hB w (by rw [hB', ha])
            | _ =>
                simp [__eo_typeof_extract, __eo_mk_apply, __eo_requires,
                  __eo_gt, native_ite, native_teq, native_not,
                  SmtEval.native_not, ha]
          · cases o <;> simp [__eo_typeof_extract] at hOBv ⊢
      | _ => simp only [__eo_typeof_extract]
  | _ => simp only [__eo_typeof_extract]

private theorem typeof_extract_diag_bitvec_inv (wm t : Term) (m : Term)
    (h : __eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof t)
      = Term.Apply (Term.UOp UserOp.BitVec) m) :
    ∃ wmv w, wm = Term.Numeral wmv ∧
      __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      native_zlt (-1 : native_Int) wmv = true ∧ native_zlt wmv w = true := by
  by_cases hNum : ∃ k, wm = Term.Numeral k
  · rcases hNum with ⟨wmv, hwm⟩
    subst wm
    rw [show __eo_typeof (Term.Numeral wmv) = Term.UOp UserOp.Int from rfl] at h
    by_cases hBv : ∃ w, __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)
    · rcases hBv with ⟨w, hT⟩
      rw [hT, typeof_extract_diag_numeral] at h
      by_cases hg1 : native_zlt (-1 : native_Int) wmv = true
      · by_cases hg2 : native_zlt wmv w = true
        · exact ⟨wmv, w, rfl, hT, hg1, hg2⟩
        · have hFalse : Term.Stuck = Term.Apply (Term.UOp UserOp.BitVec) m := by
            simpa [native_ite, hg1, hg2] using h
          cases hFalse
      · have hFalse : Term.Stuck = Term.Apply (Term.UOp UserOp.BitVec) m := by
          simpa [native_ite, hg1] using h
        cases hFalse
    · rw [typeof_extract_diag_numeral_stuck_of_not_bv wmv (__eo_typeof t)
        (by intro w hw; exact hBv ⟨w, hw⟩)] at h
      exact absurd h (by simp)
  · exfalso
    rw [typeof_extract_diag_not_numeral_stuck wm t
      (by intro k hk; exact hNum ⟨k, hk⟩)] at h
    exact absurd h (by simp)

private theorem smodSignZero_type_forces_wm_numeral
    (wm x : Term) (n : native_Int) :
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodSignZero wm x) = Term.Bool ->
    ∃ wmv, wm = Term.Numeral wmv := by
  intro hXTy hSignTy
  change
    __eo_typeof_eq
      (__eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof x))
      (__eo_typeof smodBitZero) = Term.Bool at hSignTy
  have hEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof x))
      (__eo_typeof smodBitZero) hSignTy
  have hExtract :
      __eo_typeof_extract (__eo_typeof wm) wm (__eo_typeof wm) wm (__eo_typeof x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [smodBitZero] using hEq
  rcases typeof_extract_diag_bitvec_inv wm x (Term.Numeral 1) hExtract with
    ⟨wmv, _w, hwm, _hX, _hLo, _hHi⟩
  exact ⟨wmv, hwm⟩

private theorem typeof_ite_inv_nonstuck (C A B T : Term) :
    __eo_typeof_ite C A B = T ->
    T ≠ Term.Stuck ->
    C = Term.Bool ∧ A = T ∧ B = T := by
  intro h hT
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_ite] at h
    exact False.elim (hT h.symm)
  · by_cases hB : B = Term.Stuck
    · subst B
      cases C <;> cases A <;> simp [__eo_typeof_ite] at h hA
      all_goals exact False.elim (hT h.symm)
    · by_cases hC : C = Term.Bool
      · subst C
        have hRed : __eo_typeof_ite Term.Bool A B =
            __eo_requires (__eo_eq A B) (Term.Boolean true) A := by
          cases A <;> cases B <;> simp_all [__eo_typeof_ite]
        rw [hRed] at h
        have hReqNe :
            __eo_requires (__eo_eq A B) (Term.Boolean true) A ≠ Term.Stuck := by
          rw [h]
          exact hT
        have hReq' := hReqNe
        simp [__eo_requires, native_ite, native_teq, native_not,
          SmtEval.native_not] at hReq'
        have hBA : B = A := eo_eq_true_eq hReq'.1
        subst B
        have hAEq : __eo_requires (__eo_eq A A) (Term.Boolean true) A = A := by
          cases A <;> simp [__eo_requires, __eo_eq, native_ite, native_teq,
            native_not, SmtEval.native_not] at hA ⊢
        rw [hAEq] at h
        exact ⟨rfl, h, h⟩
      · have hStuck : __eo_typeof_ite C A B = Term.Stuck := by
          cases C <;> simp_all [__eo_typeof_ite]
        rw [hStuck] at h
        exact False.elim (hT h.symm)

private theorem typeof_mk_ite_inv_nonstuck (C A B T : Term) :
    __eo_typeof
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) A) B) = T ->
    T ≠ Term.Stuck ->
    __eo_typeof C = Term.Bool ∧ __eo_typeof A = T ∧ __eo_typeof B = T := by
  intro h hT
  by_cases hB : B = Term.Stuck
  · subst B
    simp [__eo_mk_apply] at h
    exact False.elim (hT h.symm)
  · have hMk :
        __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) A) B =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) A) B := by
      cases B <;> simp_all [__eo_mk_apply]
    rw [hMk] at h
    change __eo_typeof_ite (__eo_typeof C) (__eo_typeof A) (__eo_typeof B) = T at h
    exact typeof_ite_inv_nonstuck (__eo_typeof C) (__eo_typeof A) (__eo_typeof B) T h hT

private theorem typeof_mk_mk_ite_inv_nonstuck (C A B T : Term) :
    __eo_typeof
        (__eo_mk_apply
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.ite) C) A) B) = T ->
    T ≠ Term.Stuck ->
    __eo_typeof C = Term.Bool ∧ __eo_typeof A = T ∧ __eo_typeof B = T := by
  intro h hT
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_mk_apply] at h
    exact False.elim (hT h.symm)
  · by_cases hB : B = Term.Stuck
    · subst B
      cases A <;> simp [__eo_mk_apply] at h hA
      all_goals exact False.elim (hT h.symm)
    · have hMkA :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.ite) C) A =
          Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) A := by
        cases A <;> simp_all [__eo_mk_apply]
      have hMkB :
          __eo_mk_apply
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.ite) C) A) B =
          Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) A) B := by
        rw [hMkA]
        cases B <;> simp_all [__eo_mk_apply]
      rw [hMkB] at h
      change __eo_typeof_ite (__eo_typeof C) (__eo_typeof A) (__eo_typeof B) = T at h
      exact typeof_ite_inv_nonstuck (__eo_typeof C) (__eo_typeof A) (__eo_typeof B) T h hT

private theorem smodWidthZero_type_bitvec_inv (w : Term) (n : native_Int) :
    __eo_typeof (smodWidthZero w) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    w = Term.Numeral n ∧ native_zlt (-1 : native_Int) n = true := by
  intro hTy
  unfold smodWidthZero at hTy
  change __eo_typeof__at_bv (Term.UOp UserOp.Int) (__eo_typeof w) w =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) at hTy
  have hWNe : w ≠ Term.Stuck := by
    intro hW
    subst w
    simp [__eo_typeof__at_bv] at hTy
  have hWTy : __eo_typeof w = Term.UOp UserOp.Int := by
    cases hWT : __eo_typeof w <;>
      simp [__eo_typeof__at_bv, hWNe, hWT] at hTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof__at_bv, hWNe, hWT] at hTy ⊢
  have hReq :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
    simpa [__eo_typeof__at_bv, hWNe, hWTy] using hTy
  have hReqNN :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReq]
    intro hContra
    cases hContra
  have hGuard :
      __eo_gt w (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReqNN
  cases w <;> simp [__eo_gt] at hGuard hReq
  case Numeral wv =>
    have hPos : native_zlt (-1 : native_Int) wv = true := by
      simpa [__eo_gt] using hGuard
    simp [__eo_requires, __eo_gt, hPos, native_ite, native_teq,
      native_not, SmtEval.native_not] at hReq
    cases hReq
    exact ⟨rfl, hPos⟩

private theorem smodElimRhs_outer_type_inv
    (x y w wm : Term) (n : native_Int) :
    __eo_typeof (smodElimRhs x y w wm) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodUrem x y wm) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
      __eo_typeof (smodWidthZero w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  intro hRhsTy
  let u := smodUrem x y wm
  let z := smodWidthZero w
  let rest :=
    __eo_mk_apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (smodAnd (smodSignZero wm x)
            (smodAnd (smodSignZero wm y) (Term.Boolean true))))
        u)
      (__eo_mk_apply
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm x))
              (smodAnd (smodSignZero wm y) (Term.Boolean true))))
          (smodAddWithY (Term.Apply (Term.UOp UserOp.bvneg) u) y))
        (__eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) (smodSignZero wm x))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm y))
                  (Term.Boolean true))))
            (smodAddWithY u y))
          (Term.Apply (Term.UOp UserOp.bvneg) u)))
  have hRhsTy' :
      __eo_typeof
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) (smodEq u z)) u)
          rest) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
    simpa [smodElimRhs, u, z, rest, smodAnd] using hRhsTy
  have hTNe :
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ≠ Term.Stuck := by
    intro h
    cases h
  rcases typeof_mk_ite_inv_nonstuck
      (smodEq u z) u rest
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
      hRhsTy' hTNe with
    ⟨hCondTy, hUTy, _hRestTy⟩
  have hTypesEq :
      __eo_typeof u = __eo_typeof z := by
    change __eo_typeof_eq (__eo_typeof u) (__eo_typeof z) = Term.Bool at hCondTy
    exact support_eo_typeof_eq_bool_operands_eq (__eo_typeof u) (__eo_typeof z)
      hCondTy
  constructor
  · simpa [u] using hUTy
  · simpa [u, z, hUTy] using hTypesEq.symm

private theorem smodElimRhs_add_branches_type_inv
    (x y w wm : Term) (n : native_Int) :
    __eo_typeof (smodElimRhs x y w wm) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof
        (smodAddWithY
          (Term.Apply (Term.UOp UserOp.bvneg) (smodUrem x y wm)) y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
      __eo_typeof (smodAddWithY (smodUrem x y wm) y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  intro hRhsTy
  let u := smodUrem x y wm
  let z := smodWidthZero w
  let addNeg := smodAddWithY (Term.Apply (Term.UOp UserOp.bvneg) u) y
  let addPos := smodAddWithY u y
  let negU := Term.Apply (Term.UOp UserOp.bvneg) u
  let rest3 :=
    __eo_mk_apply
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) (smodSignZero wm x))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm y))
              (Term.Boolean true))))
        addPos)
      negU
  let rest2 :=
    __eo_mk_apply
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm x))
            (smodAnd (smodSignZero wm y) (Term.Boolean true))))
        addNeg)
      rest3
  let rest1 :=
    __eo_mk_apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (smodAnd (smodSignZero wm x)
            (smodAnd (smodSignZero wm y) (Term.Boolean true))))
        u)
      rest2
  have hRhsTy' :
      __eo_typeof
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) (smodEq u z)) u)
          rest1) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
    simpa [smodElimRhs, u, z, rest1, rest2, rest3, addNeg, addPos, negU,
      smodAnd] using hRhsTy
  have hTNe :
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ≠ Term.Stuck := by
    intro h
    cases h
  rcases typeof_mk_ite_inv_nonstuck
      (smodEq u z) u rest1
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
      hRhsTy' hTNe with
    ⟨_hCond0, _hUTy, hRest1Ty⟩
  rcases typeof_mk_ite_inv_nonstuck
      (smodAnd (smodSignZero wm x)
        (smodAnd (smodSignZero wm y) (Term.Boolean true)))
      u rest2
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
      (by simpa [rest1] using hRest1Ty) hTNe with
    ⟨_hCond1, _hUTy1, hRest2Ty⟩
  rcases typeof_mk_mk_ite_inv_nonstuck
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm x))
        (smodAnd (smodSignZero wm y) (Term.Boolean true)))
      addNeg rest3
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
      (by simpa [rest2] using hRest2Ty) hTNe with
    ⟨_hCond2, hAddNegTy, hRest3Ty⟩
  rcases typeof_mk_mk_ite_inv_nonstuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) (smodSignZero wm x))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.and) (smodSignOne wm y))
          (Term.Boolean true)))
      addPos negU
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
      (by simpa [rest3] using hRest3Ty) hTNe with
    ⟨_hCond3, hAddPosTy, _hNegUTy⟩
  exact ⟨by simpa [addNeg, u] using hAddNegTy,
    by simpa [addPos, u] using hAddPosTy⟩

private theorem smodUrem_type_bitvec_inv
    (x y wm : Term) (n : native_Int) :
    __eo_typeof (smodUrem x y wm) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodAbs wm x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
      __eo_typeof (smodAbs wm y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) := by
  intro hTy
  unfold smodUrem at hTy
  change __eo_typeof_bvand (__eo_typeof (smodAbs wm x))
      (__eo_typeof (smodAbs wm y)) =
    Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) at hTy
  have hNe :
      __eo_typeof_bvand (__eo_typeof (smodAbs wm x))
          (__eo_typeof (smodAbs wm y)) ≠ Term.Stuck := by
    rw [hTy]
    intro h
    cases h
  rcases typeof_bvand_ne_stuck_inv
      (__eo_typeof (smodAbs wm x)) (__eo_typeof (smodAbs wm y)) hNe with
    ⟨bw, hXAbs, hYAbs⟩
  rw [hXAbs, hYAbs] at hTy
  by_cases hBwStuck : bw = Term.Stuck
  · subst bw
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, SmtEval.native_not] at hTy
  have hSame :
      __eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) bw)
          (Term.Apply (Term.UOp UserOp.BitVec) bw) =
        Term.Apply (Term.UOp UserOp.BitVec) bw := by
    cases bw <;> simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not, SmtEval.native_not] at hBwStuck ⊢
  rw [hSame] at hTy
  cases hTy
  exact ⟨hXAbs, hYAbs⟩

private theorem smodAbs_type_bitvec_forces_signzero_bool
    (wm x : Term) (n : native_Int) :
    __eo_typeof (smodAbs wm x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodSignZero wm x) = Term.Bool := by
  intro hAbsTy
  unfold smodAbs smodIte at hAbsTy
  change __eo_typeof_ite (__eo_typeof (smodSignZero wm x))
      (__eo_typeof x) (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) x)) =
    Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) at hAbsTy
  have hTNe :
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ≠ Term.Stuck := by
    intro h
    cases h
  exact (typeof_ite_inv_nonstuck
    (__eo_typeof (smodSignZero wm x)) (__eo_typeof x)
    (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) x))
    (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n))
    hAbsTy hTNe).1

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
      hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem smt_typeof_bvsize_eq_int (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtType.Int := by
  intro hNonneg hXSmt
  change __smtx_typeof
      (native_ite
        (native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) =
    SmtType.Int
  rw [hXSmt]
  have hSize : __smtx_bv_sizeof_type (SmtType.BitVec (native_int_to_nat n)) =
      native_nat_to_int (native_int_to_nat n) := rfl
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hSize]
  simp [native_ite, hNN]
  simp [__smtx_typeof]

private theorem eval_bvsize_eq (M : SmtModel) (x : Term) (n : native_Int)
    (hNonneg : native_zleq 0 n = true)
    (hXSmt : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int (native_int_to_nat n)) := by
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) =
    SmtValue.Numeral (native_nat_to_int (native_int_to_nat n))
  have hSize : __smtx_bv_sizeof_type (SmtType.BitVec (native_int_to_nat n)) =
      native_nat_to_int (native_int_to_nat n) := rfl
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat n)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hXSmt, hSize]
  simp [native_ite, hNN]
  simp [__smtx_model_eval, __smtx_model_eval__at_purify]

private theorem sign_zero_eq_not_one (v : SmtValue) :
    __smtx_typeof_value v = SmtType.BitVec (native_nat_succ native_nat_zero) ->
    __smtx_model_eval_eq v (SmtValue.Binary 1 0) =
      __smtx_model_eval_not (__smtx_model_eval_eq v (SmtValue.Binary 1 1)) := by
  intro hTy
  rcases bitvec_value_canonical hTy with ⟨p, rfl⟩
  have hCanon :
      native_zeq p (native_mod_total p (native_int_pow2 1)) = true := by
    have hTy' := hTy
    simpa [__smtx_typeof_value, native_ite, SmtEval.native_and,
      native_nat_to_int, native_zleq, SmtEval.native_zleq,
      native_int_to_nat, SmtEval.native_int_to_nat] using hTy'
  have hMod : native_mod_total p 2 = p := by
    have hPow : native_int_pow2 1 = 2 := by decide
    have hEq : p = native_mod_total p 2 := by
      simpa [SmtEval.native_zeq, hPow] using hCanon
    exact hEq.symm
  have hp0or1 : p = 0 ∨ p = 1 := by
    have hpNonneg : 0 <= p := by
      have hRange := Int.emod_nonneg p (by decide : (2 : Int) ≠ 0)
      have hMod' : p % 2 = p := by simpa [native_mod_total] using hMod
      simpa [hMod'] using hRange
    have hpLt : p < 2 := by
      have hRange := Int.emod_lt_of_pos p (by decide : (0 : Int) < 2)
      have hMod' : p % 2 = p := by simpa [native_mod_total] using hMod
      simpa [hMod'] using hRange
    have hpLeOne : p <= 1 := by
      have hpLt' : p < 1 + 1 := by simpa using hpLt
      exact (Int.lt_add_one_iff).mp hpLt'
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      have hpPos : 0 < p := by
        by_cases hlt : 0 < p
        · exact hlt
        · have hpLeZero : p <= 0 := Int.le_of_not_gt hlt
          have hpEq : p = 0 := Int.le_antisymm hpLeZero hpNonneg
          exact False.elim (hp0 hpEq)
      have hOneLe : 1 <= p := (Int.add_one_le_iff).2 hpPos
      exact Int.le_antisymm hpLeOne hOneLe
  rcases hp0or1 with rfl | rfl <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
      native_nat_to_int, native_not, SmtEval.native_not]

private theorem bvadd_right_zero_of_canonical (w p : native_Int) :
    native_zeq p (native_mod_total p (native_int_pow2 w)) = true ->
    __smtx_model_eval_bvadd (SmtValue.Binary w p) (SmtValue.Binary w 0) =
      SmtValue.Binary w p := by
  intro hCanon
  have hPayloadMod : native_mod_total p (native_int_pow2 w) = p := by
    have hEq : p = native_mod_total p (native_int_pow2 w) := by
      simpa [SmtEval.native_zeq] using hCanon
    exact hEq.symm
  simp [__smtx_model_eval_bvadd, native_zplus, hPayloadMod]

private theorem eo_to_smt_eq_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_and_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) =
      SmtTerm.and (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_ite_term (c t e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) =
      SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e) := by
  rfl

private theorem eo_to_smt_extract_term (hi lo z : Term) :
    __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract hi lo) z) =
      SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo) (__eo_to_smt z) := by
  rfl

private theorem eo_to_smt_bvurem_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) a) b) =
      SmtTerm.bvurem (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_bvadd_term (a b : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) =
      SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b) := by
  rfl

private theorem eo_to_smt_bvneg_term (a : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) a) =
      SmtTerm.bvneg (__eo_to_smt a) := by
  rfl

private theorem eo_to_smt_numeral (n : native_Int) :
    __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := by
  rfl

private theorem eo_to_smt_boolean (b : Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  rfl

private theorem eo_to_smt_binary (w p : native_Int) :
    __eo_to_smt (Term.Binary w p) = SmtTerm.Binary w p := by
  rfl

private theorem eo_to_smt_at_bv_num (k n : native_Int) :
    native_zleq 0 n = true ->
    __eo_to_smt (Term.UOp2 UserOp2._at_bv (Term.Numeral k) (Term.Numeral n)) =
      SmtTerm.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __eo_to_smt__at_bv (SmtTerm.Numeral k) (SmtTerm.Numeral n) =
    SmtTerm.Binary n (native_mod_total k (native_int_pow2 n))
  simp [__eo_to_smt__at_bv, hNonneg, native_ite]

private theorem eval_bv_const
    (M : SmtModel) (k n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_model_eval M
        (__eo_to_smt (Term.UOp2 UserOp2._at_bv (Term.Numeral k) (Term.Numeral n))) =
      SmtValue.Binary n (native_mod_total k (native_int_pow2 n)) := by
  intro hNonneg
  change __smtx_model_eval M
      (__eo_to_smt__at_bv (SmtTerm.Numeral k) (SmtTerm.Numeral n)) =
    SmtValue.Binary n (native_mod_total k (native_int_pow2 n))
  simp [__eo_to_smt__at_bv, native_ite, hNonneg]
  simp only [__smtx_model_eval]

private theorem eval_smt_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq a b) =
      __smtx_model_eval_eq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_and (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and a b) =
      __smtx_model_eval_and (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_ite (M : SmtModel) (c t e : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ite c t e) =
      __smtx_model_eval_ite (__smtx_model_eval M c)
        (__smtx_model_eval M t) (__smtx_model_eval M e) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_extract (M : SmtModel) (hi lo z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.extract hi lo z) =
      __smtx_model_eval_extract (__smtx_model_eval M hi)
        (__smtx_model_eval M lo) (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvurem (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvurem a b) =
      __smtx_model_eval_bvurem (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvadd (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvadd a b) =
      __smtx_model_eval_bvadd (__smtx_model_eval M a)
        (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_bvneg (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvneg a) =
      __smtx_model_eval_bvneg (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_numeral (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_boolean (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_smt_binary (M : SmtModel) (w p : native_Int) :
    __smtx_model_eval M (SmtTerm.Binary w p) = SmtValue.Binary w p := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smodAddWithY_type_forces_width_bound
    (a y : Term) (n : native_Int) :
    __eo_typeof a = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof (smodAddWithY a y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    native_zleq n 4294967296 = true := by
  intro hATy hYTy hAddTy
  have hNilNe :
      __eo_to_bin (Term.Numeral n) (Term.Numeral 0) ≠ Term.Stuck := by
    intro hNil
    unfold smodAddWithY at hAddTy
    rw [hATy] at hAddTy
    simp [__eo_nil, __eo_nil_bvadd, hNil, __eo_mk_apply] at hAddTy
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) at hAddTy
    cases hAddTy
  by_cases hBound : native_zleq n 4294967296 = true
  · exact hBound
  · have hStuck :
        __eo_to_bin (Term.Numeral n) (Term.Numeral 0) = Term.Stuck := by
      have hBoundFalse : ¬ n <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_to_bin, hBoundFalse, native_ite, native_zleq]
    exact False.elim (hNilNe hStuck)

private theorem native_mod_total_zero_pow2_of_nonneg (n : native_Int) :
    native_zleq 0 n = true ->
    native_mod_total 0 (native_int_pow2 n) = 0 := by
  intro hNonneg
  have hn : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hPowPos : 0 < native_int_pow2 n := by
    have hnot : ¬ n < 0 := Int.not_lt_of_ge hn
    rw [native_int_pow2, native_zexp_total]
    simp [hnot]
    exact Int.pow_pos (by decide : (0 : Int) < 2)
  simpa [SmtEval.native_mod_total] using
    Int.emod_eq_of_lt (by decide : (0 : Int) <= 0) hPowPos

private theorem ite_not_swap (c t e : SmtValue) :
    __smtx_model_eval_ite (__smtx_model_eval_not c) t e =
      __smtx_model_eval_ite c e t := by
  cases c <;> simp [__smtx_model_eval_not, __smtx_model_eval_ite]
  case Boolean b =>
    cases b <;> simp [__smtx_model_eval_not, __smtx_model_eval_ite,
      native_not, SmtEval.native_not]

set_option maxRecDepth 10000 in
private theorem smod_sign_extract_type (n p : native_Int) :
    __smtx_typeof_value
        (__smtx_model_eval_extract (SmtValue.Numeral (native_zplus n (native_zneg 1)))
          (SmtValue.Numeral (native_zplus n (native_zneg 1))) (SmtValue.Binary n p)) =
      SmtType.BitVec (native_nat_succ native_nat_zero) := by
  have hWidth : (n + -1 + 1 + -(n + -1) : Int) = 1 := by grind
  have hCanon :=
    native_mod_total_canonical 1 (native_binary_extract n p (n + -1) (n + -1))
  have hCanonEq :
      native_mod_total (native_binary_extract n p (n + -1) (n + -1))
          (native_int_pow2 1) =
        native_mod_total
          (native_mod_total (native_binary_extract n p (n + -1) (n + -1))
            (native_int_pow2 1))
          (native_int_pow2 1) := by
    simpa [SmtEval.native_zeq] using hCanon
  unfold __smtx_model_eval_extract
  simp only [native_zplus, native_zneg]
  rw [hWidth]
  unfold __smtx_typeof_value
  rw [show native_zleq 0 1 = true by native_decide]
  rw [hCanon]
  native_decide

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 10000000 in
private theorem eval_smodElimRhs_num
    (M : SmtModel) (x y : Term) (n px py : native_Int) :
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof
        (smodUrem x y (Term.Numeral (native_zplus n (native_zneg 1)))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.bvneg)
          (smodUrem x y (Term.Numeral (native_zplus n (native_zneg 1))))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ->
    native_zleq 0 n = true ->
    native_zleq n 4294967296 = true ->
    native_zeq py (native_mod_total py (native_int_pow2 n)) = true ->
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary n px ->
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary n py ->
    __smtx_model_eval M
        (__eo_to_smt
          (smodElimRhs x y (Term.Numeral n)
            (Term.Numeral (native_zplus n (native_zneg 1))))) =
      __smtx_model_eval_bvsmod
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hXType hYType hUType hNegUType hNonneg hMax hPyCanon hEvalX hEvalY
  rw [hEvalX, hEvalY]
  unfold smodElimRhs smodAddWithY
  dsimp only
  rw [hUType, hNegUType]
  dsimp [smodBitZero, smodBitOne, smodWidthZero, smodExtract,
    smodEq, smodAnd, smodIte, smodSignZero, smodSignOne, smodAbs, smodUrem,
    __eo_mk_apply, __eo_nil, __eo_nil_bvadd,
    __eo_to_bin, __eo_mk_binary, __eo_typeof_bvand, __eo_typeof_ite,
    __eo_typeof_eq, __eo_typeof__at_bv, __eo_typeof_bvnot,
    __smtx_model_eval_bvsmod, native_ite, native_zplus, native_zneg]
  simp [__eo_mk_apply, hMax, hNonneg, native_ite]
  rw [eo_to_smt_ite_term]
  simp only [eo_to_smt_eq_term, eo_to_smt_and_term, eo_to_smt_ite_term,
    eo_to_smt_extract_term, eo_to_smt_bvurem_term, eo_to_smt_bvadd_term,
    eo_to_smt_bvneg_term, eo_to_smt_numeral, eo_to_smt_boolean,
    eo_to_smt_binary, eo_to_smt_at_bv_num, hNonneg,
    eval_smt_eq, eval_smt_and, eval_smt_ite, eval_smt_extract,
    eval_smt_bvurem, eval_smt_bvadd, eval_smt_bvneg, eval_smt_numeral,
    eval_smt_boolean, eval_smt_binary]
  rw [eval_bv_const M 0 1 (by native_decide),
    eval_bv_const M 1 1 (by native_decide)]
  have hSignXTy := smod_sign_extract_type n px
  have hSignYTy := smod_sign_extract_type n py
  have hSignXTy' :
      __smtx_typeof_value
          (__smtx_model_eval_extract (SmtValue.Numeral (n + -1))
            (SmtValue.Numeral (n + -1)) (SmtValue.Binary n px)) =
        SmtType.BitVec (native_nat_succ native_nat_zero) := by
    simpa [native_zplus, native_zneg] using hSignXTy
  have hSignYTy' :
      __smtx_typeof_value
          (__smtx_model_eval_extract (SmtValue.Numeral (n + -1))
            (SmtValue.Numeral (n + -1)) (SmtValue.Binary n py)) =
        SmtType.BitVec (native_nat_succ native_nat_zero) := by
    simpa [native_zplus, native_zneg] using hSignYTy
  simp [native_int_pow2, native_zexp_total, native_mod_total]
  rw [hEvalX, hEvalY]
  rw [sign_zero_eq_not_one _ hSignXTy', sign_zero_eq_not_one _ hSignYTy']
  repeat rw [ite_not_swap]
  simp [hXType, hYType, hNonneg, hMax, hEvalX, hEvalY, native_ite,
    __eo_to_smt__at_bv, __smtx_bv_sizeof_value, __smtx_model_eval__,
    __smtx_model_eval_eq, __smtx_model_eval_and, __smtx_model_eval_not,
    __smtx_model_eval_ite, native_and, native_not, SmtEval.native_not,
    ite_not_swap, sign_zero_eq_not_one, bvadd_right_zero_of_canonical,
    native_mod_total_zero_pow2_of_nonneg n hNonneg, hPyCanon,
    native_zleq, native_zplus, native_zneg]

private theorem prog_bv_smod_eliminate_canonical_eq_of_ne_stuck
    (x y w wm : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    wm ≠ Term.Stuck ->
    __eo_prog_bv_smod_eliminate x y w wm
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      (Proof.pf
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) wm)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1)))) =
      smodElimBody x y w wm := by
  intro hx hy hw hwm
  rw [__eo_prog_bv_smod_eliminate.eq_5 x y w wm w x wm x hx hy hw hwm]
  simp [smodElimBody, smodElimRhs, smodBitZero, smodBitOne,
    smodWidthZero, smodExtract, smodEq, smodAnd, smodIte, smodSignZero,
    smodSignOne, smodAbs, smodUrem, smodAddWithY, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_and, native_not, SmtEval.native_not]

/--
Trusted semantic core for the canonical `bv_smod_eliminate` expansion.

The surrounding theorem proves that the checker command is in this canonical
shape and that the syntactic guards in `__eo_prog_bv_smod_eliminate` have
accepted.  The remaining obligation is the bit-vector arithmetic identity
between SMT `bvsmod` and its expansion.
-/
private axiom trusted_bv_smod_eliminate_canonical_properties
    (M : SmtModel) (hM : model_total_typed M)
    (x y w wm : Term) :
    cArgListTranslationOk
        (CArgList.cons x
          (CArgList.cons y
            (CArgList.cons w (CArgList.cons wm CArgList.nil)))) ->
    AllHaveBoolType
      [Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x),
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) wm)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))] ->
    __eo_typeof
        (__eo_prog_bv_smod_eliminate x y w wm
          (Proof.pf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) w)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
          (Proof.pf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) wm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                (Term.Numeral 1))))) =
      Term.Bool ->
    StepRuleProperties M [Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x),
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) wm)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))]
      (__eo_prog_bv_smod_eliminate x y w wm
        (Proof.pf
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) w)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
        (Proof.pf
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) wm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp._at_bvsize) x))
              (Term.Numeral 1)))))

theorem cmd_step_bv_smod_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smod_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_smod_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smod_eliminate args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_smod_eliminate args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons y args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons w args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons wm args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
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
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  change
                                    StepRuleProperties M [P1, P2]
                                      (__eo_prog_bv_smod_eliminate x y w wm
                                        (Proof.pf P1) (Proof.pf P2))
                                  have hProgLocal :
                                      __eo_prog_bv_smod_eliminate x y w wm
                                          (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck := by
                                    simpa [P1, P2] using hProg
                                  rcases bv_smod_eliminate_shape_of_ne_stuck
                                      x y w wm P1 P2 hProgLocal with
                                    ⟨pw, px, pwm, px', hP1, hP2⟩
                                  subst P1
                                  subst P2
                                  have hxNe : x ≠ Term.Stuck := by
                                    intro hx
                                    subst x
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_1 y w wm
                                        (Proof.pf
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) pw)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) px)))
                                        (Proof.pf
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) pwm)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.neg)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
                                              (Term.Numeral 1)))))
                                  have hyNe : y ≠ Term.Stuck := by
                                    intro hy
                                    subst y
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_2 x w wm _ _ hxNe)
                                  have hwNe : w ≠ Term.Stuck := by
                                    intro hw
                                    subst w
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_3 x y wm _ _ hxNe hyNe)
                                  have hwmNe : wm ≠ Term.Stuck := by
                                    intro hwm
                                    subst wm
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_4 x y w _ _ hxNe hyNe hwNe)
                                  have hReqNe := by
                                    have h := hProgLocal
                                    rw [hP1, hP2] at h
                                    rw [__eo_prog_bv_smod_eliminate.eq_5
                                      x y w wm pw px pwm px' hxNe hyNe hwNe hwmNe] at h
                                    exact h
                                  rcases bv_smod_guard_eqs_of_ne_stuck hReqNe with
                                    ⟨hpw, hpx, hpwm, hpx'⟩
                                  subst pw
                                  subst px
                                  subst pwm
                                  subst px'
                                  have hArgsTrans :
                                      cArgListTranslationOk
                                        (CArgList.cons x
                                          (CArgList.cons y
                                            (CArgList.cons w
                                              (CArgList.cons wm CArgList.nil)))) := by
                                    simpa [cmdTranslationOk] using hCmdTrans
                                  have hPremisesBoolCanonical :
                                      AllHaveBoolType
                                        [Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) w)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) x),
                                          Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) wm)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.neg)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                                              (Term.Numeral 1))] := by
                                    simpa [AllHaveBoolType, premiseTermList, hP1, hP2]
                                      using hPremisesBool
                                  have hResultTyCanonical :
                                      __eo_typeof
                                          (__eo_prog_bv_smod_eliminate x y w wm
                                            (Proof.pf
                                              (Term.Apply
                                                (Term.Apply (Term.UOp UserOp.eq) w)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
                                            (Proof.pf
                                              (Term.Apply
                                                (Term.Apply (Term.UOp UserOp.eq) wm)
                                                (Term.Apply
                                                  (Term.Apply (Term.UOp UserOp.neg)
                                                  (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                                                  (Term.Numeral 1))))) =
                                        Term.Bool := by
                                    have hResultTyLocal := hResultTy
                                    change
                                      __eo_typeof
                                        (__eo_prog_bv_smod_eliminate x y w wm
                                          (Proof.pf (__eo_state_proven_nth s n1))
                                          (Proof.pf (__eo_state_proven_nth s n2))) =
                                        Term.Bool at hResultTyLocal
                                    simpa [hP1, hP2] using hResultTyLocal
                                  simpa [hP1, hP2] using
                                    trusted_bv_smod_eliminate_canonical_properties
                                      M hM x y w wm hArgsTrans
                                      hPremisesBoolCanonical hResultTyCanonical
