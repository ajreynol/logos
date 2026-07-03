import Cpc.Proofs.Canonical.TypeDefaultBasic

/-!
# Wf-diagonalization for the infinite datatype pump

The infinite-datatype pump needs to descend into nested datatype fields.  For
a *diagonal* datatype entry `(s, d)` (one satisfying
`__smtx_type_wf_rec (Datatype s d) (Datatype s d) = true`), a nested field
`Datatype s2 d2` of the guide `d` folds to
`TF = __smtx_type_substitute s d (Datatype s2 d2) = Datatype s2 B2`.  The
entry's own well-formedness supplies `type_wf_rec TF (Datatype s2 d2)`
(wf of the folded field against the *raw* guide).  The theorem proven here
(`wf_diag_push`) upgrades that to the *diagonal* form
`type_wf_rec TF TF = true`, so the pump can re-root at `(s2, B2)` with no
environment/stack tracking at all.

Structure:
1. a ternary *guide transport* relation `GuideTr XF TUold TUnew` (with
   cons/dt forms) whose constructors carry, as premises, exactly the facts
   needed to re-check well-formedness after replacing the guide; plus the
   mechanical transport theorem.
2. substitution-chain machinery describing how the folded side of a diagonal
   entry decomposes positionally over the raw guide, and the establishment
   of the transport relation for the diagonalization instance.
-/

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Smtm

/-! ## Pattern helpers for `__smtx_dt_cons_wf_rec` -/

private theorem dt_cons_wf_p1_iff (s : native_String) (d : SmtDatatype)
    (r : native_String) (cF cU : SmtDatatypeCons) :
    __smtx_dt_cons_wf_rec
        (SmtDatatypeCons.cons (SmtType.Datatype s d) cF)
        (SmtDatatypeCons.cons (SmtType.TypeRef r) cU) =
      __smtx_dt_cons_wf_rec cF cU := by
  simp [__smtx_dt_cons_wf_rec]

private theorem dt_cons_wf_p2_parts {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (hguard : ∀ (s : native_String) (d : SmtDatatype) (r : native_String),
      TF = SmtType.Datatype s d → TU = SmtType.TypeRef r → False)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    native_inhabited_type TF = true ∧ __smtx_type_wf_rec TF TU = true ∧
      __smtx_dt_cons_wf_rec cF cU = true := by
  cases TF <;> cases TU <;>
    first
    | exact absurd rfl (fun hEq => hguard _ _ _ rfl rfl)
    | (constructor
       · cases hInh : native_inhabited_type _ <;>
           simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]
       · constructor
         · cases hWf : __smtx_type_wf_rec _ _ <;>
             simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]
         · cases hTl : __smtx_dt_cons_wf_rec cF cU <;>
             simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and])

private theorem dt_cons_wf_p2_intro {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (hInh : native_inhabited_type TF = true)
    (hWf : __smtx_type_wf_rec TF TU = true)
    (hTail : __smtx_dt_cons_wf_rec cF cU = true) :
    __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
      (SmtDatatypeCons.cons TU cU) = true := by
  cases TF <;> cases TU <;>
    simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

/-- Replacing only the tails of a passing cons-pair keeps the head check. -/
private theorem dt_cons_wf_head_tail {TF TU : SmtType}
    {cF cU cF2 cU2 : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true)
    (hTail : __smtx_dt_cons_wf_rec cF2 cU2 = true) :
    __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF2)
      (SmtDatatypeCons.cons TU cU2) = true := by
  cases TF <;> cases TU <;>
    simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

private theorem dt_wf_sum_parts {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true ∧ __smtx_dt_wf_rec dF dU = true := by
  cases hc : __smtx_dt_cons_wf_rec cF cU <;>
    simp_all [__smtx_dt_wf_rec, native_ite]

private theorem dt_cons_wf_tail {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  by_cases hc : __smtx_dt_cons_wf_rec cF cU = true
  · exact hc
  · exfalso
    cases TF <;> cases TU <;>
      simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

/-! ## Part 1: the guide-transport relation and its transport theorem -/

mutual

/-- Guide transport at a single constructor-field position: `GuideTr XF TUo TUn`
says the guide field `TUo` may be replaced by `TUn` while preserving
`__smtx_dt_cons_wf_rec`-checkability against the folded field `XF`. -/
inductive GuideTr : SmtType → SmtType → SmtType → Prop where
  /-- unchanged guide (any folded side): all checks are literally identical. -/
  | same (XF TU : SmtType) : GuideTr XF TU TU
  /-- `TypeRef t ↦ Datatype t Bt` (substitution direction).  The folded field
  must be exactly the resolved diagonal `Datatype t Dt`; the premises carry
  the two facts the new pattern-2 check needs. -/
  | toDt {t : native_String} {Dt Bt : SmtDatatype} :
      native_inhabited_type (SmtType.Datatype t Dt) = true →
      __smtx_dt_wf_rec (__smtx_dt_substitute t Dt Dt) Bt = true →
      GuideTr (SmtType.Datatype t Dt) (SmtType.TypeRef t) (SmtType.Datatype t Bt)
  /-- `Datatype t B ↦ TypeRef t` (lift direction).  Checks strictly decrease;
  the folded field must be datatype-shaped so the new pattern-1 skip applies. -/
  | toRef {t : native_String} {B : SmtDatatype} {xs : native_String}
      {xb : SmtDatatype} :
      GuideTr (SmtType.Datatype xs xb) (SmtType.Datatype t B) (SmtType.TypeRef t)
  /-- congruent body replacement under a datatype guide node, re-rooted at the
  folded field's self-substitution. -/
  | dtRec {s2 : native_String} {XFb : SmtDatatype} {dOld dNew : SmtDatatype} :
      GuideTrDt (__smtx_dt_substitute s2 XFb XFb) dOld dNew →
      GuideTr (SmtType.Datatype s2 XFb) (SmtType.Datatype s2 dOld)
        (SmtType.Datatype s2 dNew)

inductive GuideTrDtc : SmtDatatypeCons → SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : GuideTrDtc SmtDatatypeCons.unit SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {XF TUo TUn : SmtType} {cF cUo cUn : SmtDatatypeCons} :
      GuideTr XF TUo TUn → GuideTrDtc cF cUo cUn →
      GuideTrDtc (SmtDatatypeCons.cons XF cF) (SmtDatatypeCons.cons TUo cUo)
        (SmtDatatypeCons.cons TUn cUn)

inductive GuideTrDt : SmtDatatype → SmtDatatype → SmtDatatype → Prop where
  | null : GuideTrDt SmtDatatype.null SmtDatatype.null SmtDatatype.null
  | sum {cF cUo cUn : SmtDatatypeCons} {dF dUo dUn : SmtDatatype} :
      GuideTrDtc cF cUo cUn → GuideTrDt dF dUo dUn →
      GuideTrDt (SmtDatatype.sum cF dF) (SmtDatatype.sum cUo dUo)
        (SmtDatatype.sum cUn dUn)

end

mutual

/-- Transport of `__smtx_type_wf_rec` along a guide replacement.  Only used
where the new guide is not a `TypeRef` (those conversions are consumed by
the pattern-1 skip at the cons level). -/
private theorem guideTr_wf {XF TUo TUn : SmtType}
    (hTr : GuideTr XF TUo TUn)
    (hne : ∀ t : native_String, TUn ≠ SmtType.TypeRef t)
    (hOld : __smtx_type_wf_rec XF TUo = true) :
    __smtx_type_wf_rec XF TUn = true :=
  match hTr with
  | GuideTr.same _ _ => hOld
  | GuideTr.toDt _hInh hWf => by
      simpa [__smtx_type_wf_rec] using hWf
  | GuideTr.toRef => absurd rfl (hne _)
  | @GuideTr.dtRec s2 XFb dOld dNew hBody => by
      have hOldBody :
          __smtx_dt_wf_rec (__smtx_dt_substitute s2 XFb XFb) dOld = true := by
        simpa [__smtx_type_wf_rec] using hOld
      simpa [__smtx_type_wf_rec] using guideTrDt_wf hBody hOldBody

private theorem guideTrDtc_wf {cF cUo cUn : SmtDatatypeCons}
    (hTr : GuideTrDtc cF cUo cUn)
    (hOld : __smtx_dt_cons_wf_rec cF cUo = true) :
    __smtx_dt_cons_wf_rec cF cUn = true :=
  match hTr with
  | GuideTrDtc.unit => hOld
  | @GuideTrDtc.cons XF TUo TUn cF cUo cUn hField hTail => by
      cases hField with
      | same =>
          have hTailOld : __smtx_dt_cons_wf_rec cF cUo = true := by
            cases XF <;> cases TUo <;>
              simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]
          exact dt_cons_wf_head_tail hOld (guideTrDtc_wf hTail hTailOld)
      | @toDt t Dt Bt hInh hWf =>
          have hTailOld : __smtx_dt_cons_wf_rec cF cUo = true := by
            simpa [dt_cons_wf_p1_iff] using hOld
          exact dt_cons_wf_p2_intro hInh (by simpa [__smtx_type_wf_rec] using hWf)
            (guideTrDtc_wf hTail hTailOld)
      | @toRef t B xs xb =>
          have hParts := dt_cons_wf_p2_parts
            (fun _ _ _ _ hEq => by cases hEq) hOld
          rw [dt_cons_wf_p1_iff]
          exact guideTrDtc_wf hTail hParts.2.2
      | @dtRec s2 XFb dOld dNew hBody =>
          have hParts := dt_cons_wf_p2_parts
            (fun _ _ _ _ hEq => by cases hEq) hOld
          exact dt_cons_wf_p2_intro hParts.1
            (guideTr_wf (GuideTr.dtRec hBody) (fun _ h => by cases h) hParts.2.1)
            (guideTrDtc_wf hTail hParts.2.2)

private theorem guideTrDt_wf {dF dUo dUn : SmtDatatype}
    (hTr : GuideTrDt dF dUo dUn)
    (hOld : __smtx_dt_wf_rec dF dUo = true) :
    __smtx_dt_wf_rec dF dUn = true :=
  match hTr with
  | GuideTrDt.null => hOld
  | @GuideTrDt.sum cF cUo cUn dF dUo dUn hc hd => by
      have hParts := dt_wf_sum_parts hOld
      simp [__smtx_dt_wf_rec, native_ite, guideTrDtc_wf hc hParts.1,
        guideTrDt_wf hd hParts.2]

end

/-! ## Part 2: substitution chains

A *substitution chain* is a list of `(name, payload)` pairs applied
innermost-first (head first).  The folded side of the establishment walk is
always the image of the raw guide under such a chain; `chain_descend`
describes how a chain acts on the body of a `Datatype` node (payloads are
lifted against the evolving body, same-named entries are shielded), exactly
mirroring `__smtx_type_substitute`'s recursion. -/

private abbrev SubstChain := List (native_String × SmtDatatype)

private def chain_ty : SubstChain → SmtType → SmtType
  | [], T => T
  | (s, P) :: ρ, T => chain_ty ρ (__smtx_type_substitute s P T)

private def chain_dtc : SubstChain → SmtDatatypeCons → SmtDatatypeCons
  | [], c => c
  | (s, P) :: ρ, c => chain_dtc ρ (__smtx_dtc_substitute s P c)

private def chain_dt : SubstChain → SmtDatatype → SmtDatatype
  | [], X => X
  | (s, P) :: ρ, X => chain_dt ρ (__smtx_dt_substitute s P X)

private def chain_descend : SubstChain → native_String → SmtDatatype → SubstChain
  | [], _, _ => []
  | (s, P) :: ρ, s3, X =>
      if native_streq s s3 = true then chain_descend ρ s3 X
      else (s, __smtx_dt_lift s3 X P) ::
        chain_descend ρ s3 (__smtx_dt_substitute s (__smtx_dt_lift s3 X P) X)

private theorem chain_dt_null :
    ∀ ρ : SubstChain, chain_dt ρ SmtDatatype.null = SmtDatatype.null
  | [] => rfl
  | (s, P) :: ρ => by
      simp [chain_dt, __smtx_dt_substitute, chain_dt_null ρ]

private theorem chain_dtc_unit :
    ∀ ρ : SubstChain, chain_dtc ρ SmtDatatypeCons.unit = SmtDatatypeCons.unit
  | [] => rfl
  | (s, P) :: ρ => by
      simp [chain_dtc, __smtx_dtc_substitute, chain_dtc_unit ρ]

private theorem chain_dt_sum :
    ∀ (ρ : SubstChain) (c : SmtDatatypeCons) (d : SmtDatatype),
      chain_dt ρ (SmtDatatype.sum c d) =
        SmtDatatype.sum (chain_dtc ρ c) (chain_dt ρ d)
  | [], _c, _d => rfl
  | (s, P) :: ρ, c, d => by
      simp [chain_dt, chain_dtc, __smtx_dt_substitute, chain_dt_sum ρ]

private theorem chain_dtc_cons :
    ∀ (ρ : SubstChain) (T : SmtType) (c : SmtDatatypeCons),
      chain_dtc ρ (SmtDatatypeCons.cons T c) =
        SmtDatatypeCons.cons (chain_ty ρ T) (chain_dtc ρ c)
  | [], _T, _c => rfl
  | (s, P) :: ρ, T, c => by
      simp [chain_dtc, chain_ty, __smtx_dtc_substitute, chain_dtc_cons ρ]

/-- A chain fixes any type it substitutes trivially (containers and base
types). -/
private theorem chain_ty_fix (T : SmtType)
    (hFix : ∀ (s : native_String) (P : SmtDatatype),
      __smtx_type_substitute s P T = T) :
    ∀ ρ : SubstChain, chain_ty ρ T = T
  | [] => rfl
  | (s, P) :: ρ => by
      rw [chain_ty, hFix s P, chain_ty_fix T hFix ρ]

/-- How a chain acts on a datatype node: it descends into the body with
lifted payloads. -/
private theorem chain_ty_datatype :
    ∀ (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype),
      chain_ty ρ (SmtType.Datatype s3 X) =
        SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)
  | [], _s3, _X => rfl
  | (s, P) :: ρ, s3, X => by
      cases hs : native_streq s s3 with
      | true =>
          rw [chain_ty, chain_descend]
          simp only [hs, if_pos]
          rw [show __smtx_type_substitute s P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3 X by
            simp [__smtx_type_substitute, native_ite, hs]]
          exact chain_ty_datatype ρ s3 X
      | false =>
          rw [chain_ty, chain_descend]
          simp only [hs, if_neg, Bool.false_eq_true, not_false_iff]
          rw [show __smtx_type_substitute s P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3
                (__smtx_dt_substitute s (__smtx_dt_lift s3 X P) X) by
            simp [__smtx_type_substitute, native_ite, hs]]
          rw [chain_ty_datatype ρ s3
            (__smtx_dt_substitute s (__smtx_dt_lift s3 X P) X)]
          rfl

/-- Appending an entry acts after the rest of the chain. -/
private theorem chain_dt_append_one :
    ∀ (ρ : SubstChain) (s : native_String) (Q X : SmtDatatype),
      chain_dt (ρ ++ [(s, Q)]) X = __smtx_dt_substitute s Q (chain_dt ρ X)
  | [], _s, _Q, _X => rfl
  | (s0, P0) :: ρ, s, Q, X => by
      simp only [List.cons_append, chain_dt]
      exact chain_dt_append_one ρ s Q (__smtx_dt_substitute s0 P0 X)

/-- Extend a chain across a descent into `(s3, X)`: the descended chain plus
the resolved body of the node as a final self-entry. -/
private def selfExt (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype) :
    SubstChain :=
  chain_descend ρ s3 X ++ [(s3, chain_dt (chain_descend ρ s3 X) X)]

/-! ## Positional shape: folded chain-images vs. their raw sources

`FSkelTy F H` constrains the folded side `F` exactly at positions where the
raw side `H` is a datatype node: there `F` must be a same-named datatype node
whose *diagonal fold* is again positionally related to the raw body.  Every
chain image is related to its source (`fskel_master`). -/

mutual

private inductive FSkelTy : SmtType → SmtType → Prop where
  | nondt (F H : SmtType)
      (hH : ∀ (s : native_String) (B : SmtDatatype), H ≠ SmtType.Datatype s B) :
      FSkelTy F H
  | dt {s4 : native_String} {FB HB : SmtDatatype} :
      FSkelDt (__smtx_dt_substitute s4 FB FB) HB →
      FSkelTy (SmtType.Datatype s4 FB) (SmtType.Datatype s4 HB)

private inductive FSkelDtc : SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : FSkelDtc SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TF TH : SmtType} {cF cH : SmtDatatypeCons} :
      FSkelTy TF TH → FSkelDtc cF cH →
      FSkelDtc (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons TH cH)

private inductive FSkelDt : SmtDatatype → SmtDatatype → Prop where
  | null : FSkelDt SmtDatatype.null SmtDatatype.null
  | sum {cF cH : SmtDatatypeCons} {dF dH : SmtDatatype} :
      FSkelDtc cF cH → FSkelDt dF dH →
      FSkelDt (SmtDatatype.sum cF dF) (SmtDatatype.sum cH dH)

end

mutual

private theorem fskel_master_ty :
    ∀ (TU : SmtType) (ρ : SubstChain), FSkelTy (chain_ty ρ TU) TU
  | SmtType.Datatype s5 HB, ρ => by
      rw [chain_ty_datatype ρ s5 HB]
      refine FSkelTy.dt ?_
      have h := fskel_master_dt HB
        (chain_descend ρ s5 HB ++
          [(s5, chain_dt (chain_descend ρ s5 HB) HB)])
      rwa [chain_dt_append_one] at h
  | SmtType.None, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Bool, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Int, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Real, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.RegLan, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.BitVec w, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Map A B, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Set A, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Seq A, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.Char, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.USort u, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.FunType A B, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.DtcAppType A B, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)
  | SmtType.TypeRef r, ρ => FSkelTy.nondt _ _ (fun _ _ h => by cases h)

private theorem fskel_master_dtc :
    ∀ (cU : SmtDatatypeCons) (ρ : SubstChain), FSkelDtc (chain_dtc ρ cU) cU
  | SmtDatatypeCons.unit, ρ => by
      rw [chain_dtc_unit]
      exact FSkelDtc.unit
  | SmtDatatypeCons.cons T c, ρ => by
      rw [chain_dtc_cons]
      exact FSkelDtc.cons (fskel_master_ty T ρ) (fskel_master_dtc c ρ)

private theorem fskel_master_dt :
    ∀ (dU : SmtDatatype) (ρ : SubstChain), FSkelDt (chain_dt ρ dU) dU
  | SmtDatatype.null, ρ => by
      rw [chain_dt_null]
      exact FSkelDt.null
  | SmtDatatype.sum c d, ρ => by
      rw [chain_dt_sum]
      exact FSkelDt.sum (fskel_master_dtc c ρ) (fskel_master_dt d ρ)

end

/-! ## Lift transport

Lifting the raw side of the positional shape relation, and transporting
well-formedness along a guide lift (checks strictly decrease: fired datatype
nodes become pattern-1 `TypeRef` skips). -/

private theorem type_lift_nondt_fix (s3 : native_String) (X : SmtDatatype)
    (H : SmtType)
    (hH : ∀ (s : native_String) (B : SmtDatatype), H ≠ SmtType.Datatype s B) :
    __smtx_type_lift s3 X H = H := by
  cases H <;> first
    | rfl
    | exact absurd rfl (hH _ _)

mutual

private theorem fskel_lift_ty (s3 : native_String) (X : SmtDatatype)
    {TF TH : SmtType} (h : FSkelTy TF TH) :
    FSkelTy TF (__smtx_type_lift s3 X TH) :=
  match h with
  | FSkelTy.nondt F H hH => by
      rw [type_lift_nondt_fix s3 X H hH]
      exact FSkelTy.nondt F H hH
  | @FSkelTy.dt s4 FB HB hBody => by
      rw [show __smtx_type_lift s3 X (SmtType.Datatype s4 HB) =
          native_ite (native_Teq (SmtType.Datatype s3 X) (SmtType.Datatype s4 HB))
            (SmtType.TypeRef s3)
            (SmtType.Datatype s4 (__smtx_dt_lift s3 X HB)) by
        simp [__smtx_type_lift]]
      cases hEq : native_Teq (SmtType.Datatype s3 X) (SmtType.Datatype s4 HB) with
      | true =>
          rw [native_ite, if_pos rfl]
          exact FSkelTy.nondt _ _ (fun _ _ h => by cases h)
      | false =>
          rw [native_ite, if_neg (by simp [hEq])]
          exact FSkelTy.dt (fskel_lift_dt s3 X hBody)

private theorem fskel_lift_dtc (s3 : native_String) (X : SmtDatatype)
    {cF cH : SmtDatatypeCons} (h : FSkelDtc cF cH) :
    FSkelDtc cF (__smtx_dtc_lift s3 X cH) :=
  match h with
  | FSkelDtc.unit => by
      rw [show __smtx_dtc_lift s3 X SmtDatatypeCons.unit =
        SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact FSkelDtc.unit
  | @FSkelDtc.cons TF TH cF cH hT hc => by
      rw [show __smtx_dtc_lift s3 X (SmtDatatypeCons.cons TH cH) =
        SmtDatatypeCons.cons (__smtx_type_lift s3 X TH)
          (__smtx_dtc_lift s3 X cH) by simp [__smtx_dtc_lift]]
      exact FSkelDtc.cons (fskel_lift_ty s3 X hT) (fskel_lift_dtc s3 X hc)

private theorem fskel_lift_dt (s3 : native_String) (X : SmtDatatype)
    {dF dH : SmtDatatype} (h : FSkelDt dF dH) :
    FSkelDt dF (__smtx_dt_lift s3 X dH) :=
  match h with
  | FSkelDt.null => by
      rw [show __smtx_dt_lift s3 X SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact FSkelDt.null
  | @FSkelDt.sum cF cH dF dH hc hd => by
      rw [show __smtx_dt_lift s3 X (SmtDatatype.sum cH dH) =
        SmtDatatype.sum (__smtx_dtc_lift s3 X cH) (__smtx_dt_lift s3 X dH) by
        simp [__smtx_dt_lift]]
      exact FSkelDt.sum (fskel_lift_dtc s3 X hc) (fskel_lift_dt s3 X hd)

end

mutual

/-- Guide transport along a lift: replacing a guide by its lift-image. -/
private theorem lift_guide_tr_ty (s3 : native_String) (X : SmtDatatype)
    {TF TH : SmtType} (h : FSkelTy TF TH) :
    GuideTr TF TH (__smtx_type_lift s3 X TH) :=
  match h with
  | FSkelTy.nondt F H hH => by
      rw [type_lift_nondt_fix s3 X H hH]
      exact GuideTr.same F H
  | @FSkelTy.dt s4 FB HB hBody => by
      rw [show __smtx_type_lift s3 X (SmtType.Datatype s4 HB) =
          native_ite (native_Teq (SmtType.Datatype s3 X) (SmtType.Datatype s4 HB))
            (SmtType.TypeRef s3)
            (SmtType.Datatype s4 (__smtx_dt_lift s3 X HB)) by
        simp [__smtx_type_lift]]
      cases hEq : native_Teq (SmtType.Datatype s3 X) (SmtType.Datatype s4 HB) with
      | true =>
          rw [native_ite, if_pos rfl]
          have hParts : s3 = s4 ∧ X = HB := by
            have := hEq
            simp [native_Teq] at this
            exact ⟨this.1, this.2⟩
          rw [hParts.1]
          exact GuideTr.toRef
      | false =>
          rw [native_ite, if_neg (by simp [hEq])]
          exact GuideTr.dtRec (lift_guide_tr_dt s3 X hBody)

private theorem lift_guide_tr_dtc (s3 : native_String) (X : SmtDatatype)
    {cF cH : SmtDatatypeCons} (h : FSkelDtc cF cH) :
    GuideTrDtc cF cH (__smtx_dtc_lift s3 X cH) :=
  match h with
  | FSkelDtc.unit => by
      rw [show __smtx_dtc_lift s3 X SmtDatatypeCons.unit =
        SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact GuideTrDtc.unit
  | @FSkelDtc.cons TF TH cF cH hT hc => by
      rw [show __smtx_dtc_lift s3 X (SmtDatatypeCons.cons TH cH) =
        SmtDatatypeCons.cons (__smtx_type_lift s3 X TH)
          (__smtx_dtc_lift s3 X cH) by simp [__smtx_dtc_lift]]
      exact GuideTrDtc.cons (lift_guide_tr_ty s3 X hT) (lift_guide_tr_dtc s3 X hc)

private theorem lift_guide_tr_dt (s3 : native_String) (X : SmtDatatype)
    {dF dH : SmtDatatype} (h : FSkelDt dF dH) :
    GuideTrDt dF dH (__smtx_dt_lift s3 X dH) :=
  match h with
  | FSkelDt.null => by
      rw [show __smtx_dt_lift s3 X SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact GuideTrDt.null
  | @FSkelDt.sum cF cH dF dH hc hd => by
      rw [show __smtx_dt_lift s3 X (SmtDatatype.sum cH dH) =
        SmtDatatype.sum (__smtx_dtc_lift s3 X cH) (__smtx_dt_lift s3 X dH) by
        simp [__smtx_dt_lift]]
      exact GuideTrDt.sum (lift_guide_tr_dtc s3 X hc) (lift_guide_tr_dt s3 X hd)

end

/-! ## Default preservation across chain images

`__smtx_type_default_rec _ (TypeRef _)` is always `NotValue`, so a successful
default never traverses a reference position.  Consequently default-success
transports from a raw source to *any* chain images (independently chosen for
the folded side and the guide side): the constructor selection that witnessed
the old default avoids every reference spot, and images only alter reference
spots and datatype-node bodies.  This yields inhabitedness of chain images of
inhabited datatypes, with no conditions on the payloads at all. -/

mutual

private theorem defpres_ty :
    ∀ (TU : SmtType) (ρF ρN ρG : SubstChain),
      __smtx_type_default_rec (chain_ty ρF TU) TU ≠ SmtValue.NotValue →
      __smtx_type_default_rec (chain_ty ρN TU) (chain_ty ρG TU) ≠
        SmtValue.NotValue
  | SmtType.None, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρF] at hOld
      simp [__smtx_type_default_rec] at hOld
  | SmtType.TypeRef r, ρF, ρN, ρG, hOld => by
      rw [rec_typeref_nv r (chain_ty ρF (SmtType.TypeRef r))] at hOld
      exact absurd rfl hOld
  | SmtType.DtcAppType A B, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρF] at hOld
      simp [__smtx_type_default_rec] at hOld
  | SmtType.Bool, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Int, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Real, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.RegLan, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.BitVec w, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Char, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Set A, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Seq A, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.USort u, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.FunType A B, ρF, ρN, ρG, hOld => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρN,
        chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) ρG]
      simp [__smtx_type_default_rec]
  | SmtType.Map A B, ρF, ρN, ρG, hOld => by
      have hFixF := chain_ty_fix (SmtType.Map A B)
        (by intro s Q; simp [__smtx_type_substitute]) ρF
      have hFixN := chain_ty_fix (SmtType.Map A B)
        (by intro s Q; simp [__smtx_type_substitute]) ρN
      have hFixG := chain_ty_fix (SmtType.Map A B)
        (by intro s Q; simp [__smtx_type_substitute]) ρG
      rw [hFixF] at hOld
      rw [hFixN, hFixG]
      simpa [__smtx_type_default_rec] using hOld
  | SmtType.Datatype b B0, ρF, ρN, ρG, hOld => by
      rw [chain_ty_datatype ρF b B0] at hOld
      rw [chain_ty_datatype ρN b B0, chain_ty_datatype ρG b B0]
      have hOld' :
          __smtx_datatype_default b
            (chain_dt (chain_descend ρF b B0) B0) native_nat_zero
            (chain_dt
              (chain_descend ρF b B0 ++
                [(b, chain_dt (chain_descend ρF b B0) B0)]) B0) B0 ≠
            SmtValue.NotValue := by
        rw [chain_dt_append_one]
        simpa [__smtx_type_default_rec] using hOld
      have h := defpres_dt B0
        (chain_descend ρF b B0 ++ [(b, chain_dt (chain_descend ρF b B0) B0)])
        (chain_descend ρN b B0 ++ [(b, chain_dt (chain_descend ρN b B0) B0)])
        (chain_descend ρG b B0)
        b (chain_dt (chain_descend ρF b B0) B0) native_nat_zero
        b (chain_dt (chain_descend ρN b B0) B0) native_nat_zero
        hOld'
      rw [chain_dt_append_one] at h
      simpa [__smtx_type_default_rec] using h

private theorem defpres_dtc :
    ∀ (cU : SmtDatatypeCons) (ρF ρN ρG : SubstChain) (v v' : SmtValue),
      v' ≠ SmtValue.NotValue →
      __smtx_datatype_cons_default v (chain_dtc ρF cU) cU ≠
        SmtValue.NotValue →
      __smtx_datatype_cons_default v' (chain_dtc ρN cU) (chain_dtc ρG cU) ≠
        SmtValue.NotValue
  | SmtDatatypeCons.unit, ρF, ρN, ρG, v, v', hv', hOld => by
      rw [chain_dtc_unit, chain_dtc_unit]
      simpa [__smtx_datatype_cons_default] using hv'
  | SmtDatatypeCons.cons TU cU, ρF, ρN, ρG, v, v', hv', hOld => by
      rw [chain_dtc_cons] at hOld
      rw [chain_dtc_cons, chain_dtc_cons]
      have hParts :
          native_veq (__smtx_type_default_rec (chain_ty ρF TU) TU)
              SmtValue.NotValue = false ∧
            __smtx_datatype_cons_default
              (SmtValue.Apply v (__smtx_type_default_rec (chain_ty ρF TU) TU))
              (chain_dtc ρF cU) cU ≠ SmtValue.NotValue := by
        by_cases hveq :
            native_veq (__smtx_type_default_rec (chain_ty ρF TU) TU)
              SmtValue.NotValue = true
        · rw [__smtx_datatype_cons_default, native_ite, if_pos hveq] at hOld
          exact absurd rfl hOld
        · have hveq' :
              native_veq (__smtx_type_default_rec (chain_ty ρF TU) TU)
                SmtValue.NotValue = false := by
            cases h : native_veq (__smtx_type_default_rec (chain_ty ρF TU) TU)
                SmtValue.NotValue <;> simp_all
          rw [__smtx_datatype_cons_default, native_ite, if_neg hveq] at hOld
          exact ⟨hveq', hOld⟩
      have hHeadOld :
          __smtx_type_default_rec (chain_ty ρF TU) TU ≠ SmtValue.NotValue := by
        intro hEq
        rw [hEq] at hParts
        simp [native_veq] at hParts
      have hHeadNew :=
        defpres_ty TU ρF ρN ρG hHeadOld
      have hHeadNewVeq :
          native_veq
            (__smtx_type_default_rec (chain_ty ρN TU) (chain_ty ρG TU))
            SmtValue.NotValue = false := by
        cases h : native_veq
            (__smtx_type_default_rec (chain_ty ρN TU) (chain_ty ρG TU))
            SmtValue.NotValue
        · rfl
        · exact absurd (by simpa [native_veq] using h) hHeadNew
      rw [__smtx_datatype_cons_default, native_ite,
        if_neg (by simp [hHeadNewVeq])]
      exact defpres_dtc cU ρF ρN ρG
        (SmtValue.Apply v (__smtx_type_default_rec (chain_ty ρF TU) TU))
        (SmtValue.Apply v'
          (__smtx_type_default_rec (chain_ty ρN TU) (chain_ty ρG TU)))
        (fun h => by cases h) hParts.2

private theorem defpres_dt :
    ∀ (DU : SmtDatatype) (ρF ρN ρG : SubstChain)
      (s : native_String) (d : SmtDatatype) (n : native_Nat)
      (s' : native_String) (d' : SmtDatatype) (n' : native_Nat),
      __smtx_datatype_default s d n (chain_dt ρF DU) DU ≠ SmtValue.NotValue →
      __smtx_datatype_default s' d' n' (chain_dt ρN DU) (chain_dt ρG DU) ≠
        SmtValue.NotValue
  | SmtDatatype.null, ρF, ρN, ρG, s, d, n, s', d', n', hOld => by
      rw [chain_dt_null] at hOld
      simp [__smtx_datatype_default] at hOld
  | SmtDatatype.sum cU DU, ρF, ρN, ρG, s, d, n, s', d', n', hOld => by
      rw [chain_dt_sum] at hOld
      rw [chain_dt_sum, chain_dt_sum]
      by_cases hNewHead :
          __smtx_datatype_cons_default (SmtValue.DtCons s' d' n')
            (chain_dtc ρN cU) (chain_dtc ρG cU) = SmtValue.NotValue
      · -- the new head constructor is not defaultable: the old head cannot
        -- have been defaultable either (else transport contradicts), so the
        -- old walk succeeded in the tail; recurse there.
        have hOldHead :
            __smtx_datatype_cons_default (SmtValue.DtCons s d n)
              (chain_dtc ρF cU) cU = SmtValue.NotValue := by
          by_cases h :
              __smtx_datatype_cons_default (SmtValue.DtCons s d n)
                (chain_dtc ρF cU) cU = SmtValue.NotValue
          · exact h
          · exact absurd
              (defpres_dtc cU ρF ρN ρG (SmtValue.DtCons s d n)
                (SmtValue.DtCons s' d' n') (fun hh => by cases hh) h)
              (by simpa using hNewHead)
        have hOldTail :
            __smtx_datatype_default s d (native_nat_succ n)
              (chain_dt ρF DU) DU ≠ SmtValue.NotValue := by
          rw [__smtx_datatype_default, native_ite,
            if_neg (by simp [hOldHead, native_veq, native_not])] at hOld
          exact hOld
        have hNewTail :=
          defpres_dt DU ρF ρN ρG s d (native_nat_succ n)
            s' d' (native_nat_succ n') hOldTail
        rw [__smtx_datatype_default, native_ite,
          if_neg (by simp [hNewHead, native_veq, native_not])]
        exact hNewTail
      · -- the new head is defaultable: the walk returns it.
        have hNewHeadVeq :
            native_not
              (native_veq
                (__smtx_datatype_cons_default (SmtValue.DtCons s' d' n')
                  (chain_dtc ρN cU) (chain_dtc ρG cU))
                SmtValue.NotValue) = true := by
          simp [native_veq, native_not, hNewHead]
        rw [__smtx_datatype_default, native_ite, if_pos hNewHeadVeq]
        exact hNewHead

end

/-- Chain images of inhabited datatypes are inhabited: the constructor
selection witnessing the source's default avoids every reference spot, and
chain substitutions only alter reference spots and datatype-node bodies. -/
private theorem inhabited_chain_image
    (t : native_String) (B : SmtDatatype) (ρ : SubstChain)
    (hInh : native_inhabited_type (SmtType.Datatype t B) = true) :
    native_inhabited_type (SmtType.Datatype t (chain_dt ρ B)) = true := by
  have hOldNe :
      __smtx_type_default (SmtType.Datatype t B) ≠ SmtValue.NotValue := by
    intro hEq
    have hTeq :
        native_Teq
          (__smtx_typeof_value (__smtx_type_default (SmtType.Datatype t B)))
          (SmtType.Datatype t B) = true := by
      simpa [native_inhabited_type, native_and, native_not, native_Teq]
        using hInh
    rw [hEq] at hTeq
    simp [__smtx_typeof_value, native_Teq] at hTeq
  have hOld :
      __smtx_datatype_default t B native_nat_zero
        (chain_dt [(t, B)] B) B ≠ SmtValue.NotValue := by
    simpa [__smtx_type_default, __smtx_type_default_rec, chain_dt]
      using hOldNe
  have hNew := defpres_dt B [(t, B)] (ρ ++ [(t, chain_dt ρ B)]) ρ
    t B native_nat_zero t (chain_dt ρ B) native_nat_zero hOld
  rw [chain_dt_append_one] at hNew
  have hNewNe :
      __smtx_type_default (SmtType.Datatype t (chain_dt ρ B)) ≠
        SmtValue.NotValue := by
    simpa [__smtx_type_default, __smtx_type_default_rec] using hNew
  rcases type_default_notvalue_or_typed (SmtType.Datatype t (chain_dt ρ B))
    with h | h
  · exact absurd h hNewNe
  · simp [native_inhabited_type, native_and, native_not, native_Teq, h]

/-! ## Reference-excused defaultability

`refDef S T` is default-success with `TypeRef` positions whose name lies in
`S` *excused* (deferred to a firing environment).  Since a real default never
traverses any reference position (`__smtx_type_default_rec _ (TypeRef _)` is
`NotValue`), real default-success implies `refDef` for any `S`; and unlike
real inhabitedness, `refDef` is *monotone under lifts* — a lift only turns
datatype nodes into references of the lift's own name, which the extended
excuse set covers.  This is the seed layer for transporting inhabitedness
onto images whose chains fire references. -/

mutual

private def refDefTy (S : RefList) : SmtType → Bool
  | SmtType.TypeRef r => native_reflist_contains S r
  | SmtType.Datatype _ B => refDefDt S B
  | SmtType.Map _ U =>
      native_not (native_veq (__smtx_type_default_rec U U) SmtValue.NotValue)
  | SmtType.None => false
  | SmtType.DtcAppType _ _ => false
  | _ => true

private def refDefDtc (S : RefList) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.unit => true
  | SmtDatatypeCons.cons T c => refDefTy S T && refDefDtc S c

private def refDefDt (S : RefList) : SmtDatatype → Bool
  | SmtDatatype.null => false
  | SmtDatatype.sum c d => refDefDtc S c || refDefDt S d

end

/-! Monotonicity of the excuse set. -/
mutual

private theorem refDefTy_mono {S S' : RefList}
    (hSub : ∀ r : native_String, native_reflist_contains S r = true →
      native_reflist_contains S' r = true) :
    ∀ TU : SmtType, refDefTy S TU = true → refDefTy S' TU = true
  | SmtType.TypeRef r, h => by
      simpa [refDefTy] using hSub r (by simpa [refDefTy] using h)
  | SmtType.Datatype b B, h => by
      simpa [refDefTy] using refDefDt_mono hSub B (by simpa [refDefTy] using h)
  | SmtType.Map T U, h => h
  | SmtType.None, h => h
  | SmtType.DtcAppType A B, h => h
  | SmtType.Bool, h => h
  | SmtType.Int, h => h
  | SmtType.Real, h => h
  | SmtType.RegLan, h => h
  | SmtType.BitVec w, h => h
  | SmtType.Char, h => h
  | SmtType.Set A, h => h
  | SmtType.Seq A, h => h
  | SmtType.USort u, h => h
  | SmtType.FunType A B, h => h

private theorem refDefDtc_mono {S S' : RefList}
    (hSub : ∀ r : native_String, native_reflist_contains S r = true →
      native_reflist_contains S' r = true) :
    ∀ cU : SmtDatatypeCons, refDefDtc S cU = true → refDefDtc S' cU = true
  | SmtDatatypeCons.unit, h => h
  | SmtDatatypeCons.cons T c, h => by
      have hp : refDefTy S T = true ∧ refDefDtc S c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using h
      simp [refDefDtc, Bool.and_eq_true,
        refDefTy_mono hSub T hp.1, refDefDtc_mono hSub c hp.2]

private theorem refDefDt_mono {S S' : RefList}
    (hSub : ∀ r : native_String, native_reflist_contains S r = true →
      native_reflist_contains S' r = true) :
    ∀ DU : SmtDatatype, refDefDt S DU = true → refDefDt S' DU = true
  | SmtDatatype.null, h => h
  | SmtDatatype.sum c d, h => by
      have hp : refDefDtc S c = true ∨ refDefDt S d = true := by
        simpa [refDefDt, Bool.or_eq_true] using h
      rcases hp with hp | hp
      · simp [refDefDt, Bool.or_eq_true, refDefDtc_mono hSub c hp]
      · simp [refDefDt, Bool.or_eq_true, refDefDt_mono hSub d hp]

end

/-! Real default-success implies reference-excused defaultability, for any
excuse set and any folded side: a successful default never sits on a
reference position. -/
mutual

private theorem refDef_of_default_ty (S : RefList) :
    ∀ (TU : SmtType) (V : SmtType),
      __smtx_type_default_rec V TU ≠ SmtValue.NotValue →
      refDefTy S TU = true
  | SmtType.TypeRef r, V, h => absurd (rec_typeref_nv r V) h
  | SmtType.None, V, h => by
      simp [__smtx_type_default_rec] at h
  | SmtType.DtcAppType A B, V, h => by
      simp [__smtx_type_default_rec] at h
  | SmtType.Bool, V, h => by simp [refDefTy]
  | SmtType.Int, V, h => by simp [refDefTy]
  | SmtType.Real, V, h => by simp [refDefTy]
  | SmtType.RegLan, V, h => by simp [refDefTy]
  | SmtType.BitVec w, V, h => by simp [refDefTy]
  | SmtType.Char, V, h => by simp [refDefTy]
  | SmtType.Set A, V, h => by simp [refDefTy]
  | SmtType.Seq A, V, h => by simp [refDefTy]
  | SmtType.USort u, V, h => by simp [refDefTy]
  | SmtType.FunType A B, V, h => by simp [refDefTy]
  | SmtType.Map T U, V, h => by
      by_cases hU :
          native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = true
      · exfalso
        cases V <;>
          simp [__smtx_type_default_rec, native_ite, hU] at h
      · simp [refDefTy, native_not]
        cases hU' : native_veq (__smtx_type_default_rec U U)
            SmtValue.NotValue
        · rfl
        · exact absurd hU' hU
  | SmtType.Datatype b B, V, h => by
      cases V with
      | Datatype a A =>
          have hB :
              __smtx_datatype_default a A native_nat_zero
                (__smtx_dt_substitute a A A) B ≠ SmtValue.NotValue := by
            simpa [__smtx_type_default_rec] using h
          simpa [refDefTy] using
            refDef_of_default_dt S B _ a A native_nat_zero hB
      | Bool => simp [__smtx_type_default_rec] at h
      | Int => simp [__smtx_type_default_rec] at h
      | Real => simp [__smtx_type_default_rec] at h
      | RegLan => simp [__smtx_type_default_rec] at h
      | BitVec w => simp [__smtx_type_default_rec] at h
      | Char => simp [__smtx_type_default_rec] at h
      | Map T U => simp [__smtx_type_default_rec] at h
      | Set T => simp [__smtx_type_default_rec] at h
      | Seq T => simp [__smtx_type_default_rec] at h
      | USort u => simp [__smtx_type_default_rec] at h
      | FunType T U => simp [__smtx_type_default_rec] at h
      | DtcAppType T U => simp [__smtx_type_default_rec] at h
      | None => simp [__smtx_type_default_rec] at h
      | TypeRef r => simp [__smtx_type_default_rec] at h

private theorem refDef_of_default_dtc (S : RefList) :
    ∀ (cU cF : SmtDatatypeCons) (v : SmtValue),
      __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue →
      refDefDtc S cU = true
  | SmtDatatypeCons.unit, cF, v, h => by simp [refDefDtc]
  | SmtDatatypeCons.cons TU cU, cF, v, h => by
      cases cF with
      | unit => simp [__smtx_datatype_cons_default] at h
      | cons TF cF =>
          by_cases hHead :
              native_veq (__smtx_type_default_rec TF TU)
                SmtValue.NotValue = true
          · rw [__smtx_datatype_cons_default, native_ite, if_pos hHead] at h
            exact absurd rfl h
          · rw [__smtx_datatype_cons_default, native_ite, if_neg hHead] at h
            have hHead' :
                __smtx_type_default_rec TF TU ≠ SmtValue.NotValue := by
              intro hEq
              rw [hEq] at hHead
              simp [native_veq] at hHead
            simp [refDefDtc, Bool.and_eq_true,
              refDef_of_default_ty S TU TF hHead',
              refDef_of_default_dtc S cU cF _ h]

private theorem refDef_of_default_dt (S : RefList) :
    ∀ (DU DF : SmtDatatype) (s : native_String) (d : SmtDatatype)
      (n : native_Nat),
      __smtx_datatype_default s d n DF DU ≠ SmtValue.NotValue →
      refDefDt S DU = true
  | SmtDatatype.null, DF, s, d, n, h => by
      cases DF <;> simp [__smtx_datatype_default] at h
  | SmtDatatype.sum cU DU, DF, s, d, n, h => by
      cases DF with
      | null => simp [__smtx_datatype_default] at h
      | sum cF DF =>
          by_cases hHead :
              __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU =
                SmtValue.NotValue
          · rw [__smtx_datatype_default, native_ite,
              if_neg (by simp [hHead, native_veq, native_not])] at h
            simp [refDefDt, Bool.or_eq_true,
              refDef_of_default_dt S DU DF s d (native_nat_succ n) h]
          · simp [refDefDt, Bool.or_eq_true,
              refDef_of_default_dtc S cU cF _ hHead]

end

/-! Reference-excused defaultability is monotone under lifts: a lift only
converts datatype nodes into references of the lift's own name. -/
mutual

private theorem refDef_lift_ty (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ TU : SmtType, refDefTy S TU = true →
      refDefTy (native_reflist_insert S s) (__smtx_type_lift s X TU) = true
  | SmtType.TypeRef r, h => by
      rw [show __smtx_type_lift s X (SmtType.TypeRef r) = SmtType.TypeRef r by
        simp [__smtx_type_lift]]
      exact refDefTy_mono
        (fun r' hr' => by
          simpa [native_reflist_contains, native_reflist_insert] using
            Or.inr (by simpa [native_reflist_contains] using hr'))
        (SmtType.TypeRef r) h
  | SmtType.Datatype b B, h => by
      rw [show __smtx_type_lift s X (SmtType.Datatype b B) =
          native_ite (native_Teq (SmtType.Datatype s X) (SmtType.Datatype b B))
            (SmtType.TypeRef s)
            (SmtType.Datatype b (__smtx_dt_lift s X B)) by
        simp [__smtx_type_lift]]
      cases hEq : native_Teq (SmtType.Datatype s X) (SmtType.Datatype b B) with
      | true =>
          rw [native_ite, if_pos rfl]
          simp [refDefTy, native_reflist_contains, native_reflist_insert]
      | false =>
          rw [native_ite, if_neg (by simp [hEq])]
          simpa [refDefTy] using
            refDef_lift_dt s X S B (by simpa [refDefTy] using h)
  | SmtType.Map T U, h => by
      rw [show __smtx_type_lift s X (SmtType.Map T U) = SmtType.Map T U by
        simp [__smtx_type_lift]]
      exact h
  | SmtType.None, h => by simp [refDefTy] at h
  | SmtType.DtcAppType A B, h => by simp [refDefTy] at h
  | SmtType.Bool, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.Int, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.Real, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.RegLan, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.BitVec w, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.Char, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.Set A, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.Seq A, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.USort u, h => by simp [__smtx_type_lift, refDefTy]
  | SmtType.FunType A B, h => by simp [__smtx_type_lift, refDefTy]

private theorem refDef_lift_dtc (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ cU : SmtDatatypeCons, refDefDtc S cU = true →
      refDefDtc (native_reflist_insert S s) (__smtx_dtc_lift s X cU) = true
  | SmtDatatypeCons.unit, h => by
      simp [__smtx_dtc_lift, refDefDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp : refDefTy S T = true ∧ refDefDtc S c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using h
      rw [show __smtx_dtc_lift s X (SmtDatatypeCons.cons T c) =
        SmtDatatypeCons.cons (__smtx_type_lift s X T)
          (__smtx_dtc_lift s X c) by simp [__smtx_dtc_lift]]
      simp [refDefDtc, Bool.and_eq_true,
        refDef_lift_ty s X S T hp.1, refDef_lift_dtc s X S c hp.2]

private theorem refDef_lift_dt (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ DU : SmtDatatype, refDefDt S DU = true →
      refDefDt (native_reflist_insert S s) (__smtx_dt_lift s X DU) = true
  | SmtDatatype.null, h => by simp [refDefDt] at h
  | SmtDatatype.sum c d, h => by
      have hp : refDefDtc S c = true ∨ refDefDt S d = true := by
        simpa [refDefDt, Bool.or_eq_true] using h
      rw [show __smtx_dt_lift s X (SmtDatatype.sum c d) =
        SmtDatatype.sum (__smtx_dtc_lift s X c) (__smtx_dt_lift s X d) by
        simp [__smtx_dt_lift]]
      rcases hp with hp | hp
      · simp [refDefDt, Bool.or_eq_true, refDef_lift_dtc s X S c hp]
      · simp [refDefDt, Bool.or_eq_true, refDef_lift_dt s X S d hp]

end

/-! ## The chain invariant and the establishment walk -/

/-- The pump invariant of a chain: its head entry `(t, P)` resolves through
the whole chain to an inhabited datatype whose diagonal fold is well-formed
against the current payload `P` and positionally related to it. -/
private def ChainOK : SubstChain → Prop
  | [] => True
  | (t, P) :: REST =>
      ∃ D : SmtDatatype,
        chain_ty ((t, P) :: REST) (SmtType.TypeRef t) = SmtType.Datatype t D ∧
        native_inhabited_type (SmtType.Datatype t D) = true ∧
        __smtx_dt_wf_rec (__smtx_dt_substitute t D D) P = true ∧
        FSkelDt (__smtx_dt_substitute t D D) P

/-- Packaging: the head entry facts for the *canonical* resolved body imply
the chain invariant; the resolution-shape and positional-skeleton components
hold generically. -/
private theorem chainok_head_facts
    (t : native_String) (P : SmtDatatype) (REST : SubstChain)
    (hFacts :
      native_inhabited_type
        (SmtType.Datatype t (chain_dt (chain_descend REST t P) P)) = true ∧
      __smtx_dt_wf_rec
        (__smtx_dt_substitute t (chain_dt (chain_descend REST t P) P)
          (chain_dt (chain_descend REST t P) P)) P = true) :
    ChainOK ((t, P) :: REST) := by
  refine ⟨chain_dt (chain_descend REST t P) P, ?_, hFacts.1, hFacts.2, ?_⟩
  · rw [show chain_ty ((t, P) :: REST) (SmtType.TypeRef t) =
        chain_ty REST (__smtx_type_substitute t P (SmtType.TypeRef t)) from rfl]
    rw [show __smtx_type_substitute t P (SmtType.TypeRef t) =
        SmtType.Datatype t P by
      simp [__smtx_type_substitute, native_ite, native_streq]]
    exact chain_ty_datatype REST t P
  · have h := fskel_master_dt P
      (chain_descend REST t P ++ [(t, chain_dt (chain_descend REST t P) P)])
    rwa [chain_dt_append_one] at h

/-- THE remaining gap: across a descent step at a well-formed inhabited node,
the head resolution is stable — or, when it is not (which requires a
shadowing/self-overlapping input), its replacement still satisfies the entry
facts.  Probed extensively (mutual/cyclic/mid-referencing descents all yield
a *stable* resolution; only descents whose binder name collides with an
enclosing binder mutate it, and even then the facts survive, using the
inhabitedness/well-formedness of the descended node). -/
private theorem chainok_selfExt_facts
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (P : SmtDatatype) (REST : SubstChain)
    (hρ : ρ = (t, P) :: REST)
    (hne : native_streq t s3 = false)
    (hOK : ChainOK ρ)
    (hInhNode :
      native_inhabited_type
        (SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)) = true)
    (hWfNode :
      __smtx_dt_wf_rec
        (__smtx_dt_substitute s3 (chain_dt (chain_descend ρ s3 X) X)
          (chain_dt (chain_descend ρ s3 X) X)) X = true)
    (hUnstable :
      chain_ty (selfExt ρ s3 X) (SmtType.TypeRef t) ≠
        chain_ty ρ (SmtType.TypeRef t)) :
    ChainOK (selfExt ρ s3 X) := by
  subst hρ
  have hSelfExt :
      selfExt ((t, P) :: REST) s3 X =
        (t, __smtx_dt_lift s3 X P) ::
          (chain_descend REST s3
            (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
            [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)]) := by
    simp [selfExt, chain_descend, hne]
  rw [hSelfExt]
  refine chainok_head_facts t (__smtx_dt_lift s3 X P)
    (chain_descend REST s3
      (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
      [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)]) ?_
  sorry

/-- The chain invariant is preserved by a descent step at a well-formed
inhabited node.  The head payload is lifted against the descent body, the
rest of the chain descends, and the resolved body of the descended node
joins as a final self-entry.  When the head resolution is stable across the
step (every case reachable from non-shadowing inputs), the facts transport
directly: the resolution is unchanged and its well-formedness follows along
the guide lift. -/
private theorem chainok_selfExt
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (P : SmtDatatype) (REST : SubstChain)
    (hρ : ρ = (t, P) :: REST)
    (hne : native_streq t s3 = false)
    (hOK : ChainOK ρ)
    (hInhNode :
      native_inhabited_type
        (SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)) = true)
    (hWfNode :
      __smtx_dt_wf_rec
        (__smtx_dt_substitute s3 (chain_dt (chain_descend ρ s3 X) X)
          (chain_dt (chain_descend ρ s3 X) X)) X = true) :
    ChainOK (selfExt ρ s3 X) := by
  by_cases hStable :
      chain_ty (selfExt ρ s3 X) (SmtType.TypeRef t) =
        chain_ty ρ (SmtType.TypeRef t)
  · -- stable resolution: transport the facts along the head-payload lift
    subst hρ
    rcases hOK with ⟨D, hRes, hInh, hWf, hSkel⟩
    -- the descended chain has head `(t, lift s3 X P)`
    have hSelfExt :
        selfExt ((t, P) :: REST) s3 X =
          (t, __smtx_dt_lift s3 X P) ::
            (chain_descend REST s3
              (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
              [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)]) := by
      simp [selfExt, chain_descend, hne]
    rw [hSelfExt]
    refine ⟨D, ?_, hInh, ?_, ?_⟩
    · rw [← hSelfExt, hStable]
      exact hRes
    · exact guideTrDt_wf (lift_guide_tr_dt s3 X hSkel) hWf
    · exact fskel_lift_dt s3 X hSkel
  · exact chainok_selfExt_facts ρ s3 X t P REST hρ hne hOK hInhNode
      hWfNode hStable

/-! The establishment walk: over a raw guide `dU`, the image under a chain
with head `(t, P)` transports the guide from `dU` to `dt_substitute t P dU`,
given the chain invariant and the old well-formedness (whose pattern-2 facts
feed the chain-invariant maintenance at nested descents). -/
mutual

private theorem estab_ty :
    ∀ (TU : SmtType) (t : native_String) (P : SmtDatatype) (REST : SubstChain),
      ChainOK ((t, P) :: REST) →
      (∀ (s3 : native_String) (X : SmtDatatype), TU = SmtType.Datatype s3 X →
        native_inhabited_type (chain_ty ((t, P) :: REST) TU) = true ∧
          __smtx_type_wf_rec (chain_ty ((t, P) :: REST) TU) TU = true) →
      GuideTr (chain_ty ((t, P) :: REST) TU) TU (__smtx_type_substitute t P TU)
  | SmtType.TypeRef r, t, P, REST, hOK, _hOldField => by
      cases hs : native_streq t r with
      | true =>
          have hEq : t = r := by simpa [native_streq] using hs
          subst r
          rcases hOK with ⟨D, hRes, hInh, hWf, _hSkel⟩
          rw [hRes]
          rw [show __smtx_type_substitute t P (SmtType.TypeRef t) =
              SmtType.Datatype t P by
            simp [__smtx_type_substitute, native_ite, native_streq]]
          exact GuideTr.toDt hInh hWf
      | false =>
          rw [show __smtx_type_substitute t P (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hs]]
          exact GuideTr.same _ _
  | SmtType.Datatype s3 X, t, P, REST, hOK, hOldField => by
      cases hs : native_streq t s3 with
      | true =>
          rw [show __smtx_type_substitute t P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3 X by
            simp [__smtx_type_substitute, native_ite, hs]]
          exact GuideTr.same _ _
      | false =>
          have hFacts := hOldField s3 X rfl
          rw [chain_ty_datatype ((t, P) :: REST) s3 X] at hFacts
          have hInhNode :
              native_inhabited_type
                (SmtType.Datatype s3
                  (chain_dt (chain_descend ((t, P) :: REST) s3 X) X)) = true :=
            hFacts.1
          have hWfNode :
              __smtx_dt_wf_rec
                (__smtx_dt_substitute s3
                  (chain_dt (chain_descend ((t, P) :: REST) s3 X) X)
                  (chain_dt (chain_descend ((t, P) :: REST) s3 X) X)) X = true := by
            simpa [__smtx_type_wf_rec] using hFacts.2
          rw [chain_ty_datatype ((t, P) :: REST) s3 X]
          rw [show __smtx_type_substitute t P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3
                (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) by
            simp [__smtx_type_substitute, native_ite, hs]]
          refine GuideTr.dtRec ?_
          -- the descended chain has head `(t, lift s3 X P)`
          have hDesc :
              chain_descend ((t, P) :: REST) s3 X =
                (t, __smtx_dt_lift s3 X P) ::
                  chain_descend REST s3
                    (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) := by
            simp [chain_descend, hs]
          have hOK' : ChainOK (selfExt ((t, P) :: REST) s3 X) :=
            chainok_selfExt ((t, P) :: REST) s3 X t P REST rfl hs hOK
              hInhNode hWfNode
          have hSelfExtEq : selfExt ((t, P) :: REST) s3 X =
              (t, __smtx_dt_lift s3 X P) ::
                (chain_descend REST s3
                  (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                  [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)]) := by
            simp [selfExt, hDesc]
          -- the folded side of the child chain is the node's diagonal fold
          have hFold :
              chain_dt
                ((t, __smtx_dt_lift s3 X P) ::
                  (chain_descend REST s3
                    (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                    [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)])) X =
                __smtx_dt_substitute s3
                  (chain_dt (chain_descend ((t, P) :: REST) s3 X) X)
                  (chain_dt (chain_descend ((t, P) :: REST) s3 X) X) := by
            rw [show ((t, __smtx_dt_lift s3 X P) ::
                (chain_descend REST s3
                  (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                  [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)])) =
              (chain_descend ((t, P) :: REST) s3 X ++
                [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)]) by
              simp [hDesc]]
            rw [chain_dt_append_one]
          have hWalk := estab_dt X t (__smtx_dt_lift s3 X P)
            (chain_descend REST s3
              (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
              [(s3, chain_dt (chain_descend ((t, P) :: REST) s3 X) X)])
            (by rwa [hSelfExtEq] at hOK')
            (by rw [hFold]; exact hWfNode)
          rwa [hFold] at hWalk
  | SmtType.None, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.None = SmtType.None by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Bool, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Bool = SmtType.Bool by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Int, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Int = SmtType.Int by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Real, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Real = SmtType.Real by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.RegLan, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.RegLan = SmtType.RegLan by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.BitVec w, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.BitVec w) = SmtType.BitVec w by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Map A B, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Map A B) = SmtType.Map A B by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Set A, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Set A) = SmtType.Set A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Seq A, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Seq A) = SmtType.Seq A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Char, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Char = SmtType.Char by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.USort u, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.USort u) = SmtType.USort u by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.FunType A B, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.DtcAppType A B, t, P, REST, _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _

private theorem estab_dtc :
    ∀ (cU : SmtDatatypeCons) (t : native_String) (P : SmtDatatype)
      (REST : SubstChain),
      ChainOK ((t, P) :: REST) →
      __smtx_dt_cons_wf_rec (chain_dtc ((t, P) :: REST) cU) cU = true →
      GuideTrDtc (chain_dtc ((t, P) :: REST) cU) cU
        (__smtx_dtc_substitute t P cU)
  | SmtDatatypeCons.unit, t, P, REST, _hOK, _hOld => by
      rw [chain_dtc_unit]
      rw [show __smtx_dtc_substitute t P SmtDatatypeCons.unit =
        SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact GuideTrDtc.unit
  | SmtDatatypeCons.cons TU cU, t, P, REST, hOK, hOld => by
      rw [chain_dtc_cons] at hOld
      have hTail : __smtx_dt_cons_wf_rec (chain_dtc ((t, P) :: REST) cU) cU = true :=
        dt_cons_wf_tail hOld
      have hOldField : ∀ (s3 : native_String) (X : SmtDatatype),
          TU = SmtType.Datatype s3 X →
          native_inhabited_type (chain_ty ((t, P) :: REST) TU) = true ∧
            __smtx_type_wf_rec (chain_ty ((t, P) :: REST) TU) TU = true := by
        intro s3 X hTU
        subst hTU
        have hParts := dt_cons_wf_p2_parts
          (fun _ _ _ _ hEq => by cases hEq) hOld
        exact ⟨hParts.1, hParts.2.1⟩
      rw [chain_dtc_cons]
      rw [show __smtx_dtc_substitute t P (SmtDatatypeCons.cons TU cU) =
        SmtDatatypeCons.cons (__smtx_type_substitute t P TU)
          (__smtx_dtc_substitute t P cU) by simp [__smtx_dtc_substitute]]
      exact GuideTrDtc.cons (estab_ty TU t P REST hOK hOldField)
        (estab_dtc cU t P REST hOK hTail)

private theorem estab_dt :
    ∀ (dU : SmtDatatype) (t : native_String) (P : SmtDatatype)
      (REST : SubstChain),
      ChainOK ((t, P) :: REST) →
      __smtx_dt_wf_rec (chain_dt ((t, P) :: REST) dU) dU = true →
      GuideTrDt (chain_dt ((t, P) :: REST) dU) dU (__smtx_dt_substitute t P dU)
  | SmtDatatype.null, t, P, REST, _hOK, _hOld => by
      rw [chain_dt_null]
      rw [show __smtx_dt_substitute t P SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_substitute]]
      exact GuideTrDt.null
  | SmtDatatype.sum cU dU, t, P, REST, hOK, hOld => by
      rw [chain_dt_sum] at hOld
      have hParts := dt_wf_sum_parts hOld
      rw [chain_dt_sum]
      rw [show __smtx_dt_substitute t P (SmtDatatype.sum cU dU) =
        SmtDatatype.sum (__smtx_dtc_substitute t P cU)
          (__smtx_dt_substitute t P dU) by simp [__smtx_dt_substitute]]
      exact GuideTrDt.sum (estab_dtc cU t P REST hOK hParts.1)
        (estab_dt dU t P REST hOK hParts.2)

end

/-- Establishment of the guide transport for the diagonalization instance:
the raw guide `dC` of a folded nested field may be replaced by the folded
body `BC = __smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC` itself.
The parent entry `(sP, dP)` is diagonal (inhabited and self-well-formed). -/
private theorem wf_diag_establish
    (sP : native_String) (dP : SmtDatatype)
    (hPInh : native_inhabited_type (SmtType.Datatype sP dP) = true)
    (hPWf : __smtx_type_wf_rec (SmtType.Datatype sP dP)
        (SmtType.Datatype sP dP) = true)
    (sC : native_String) (dC : SmtDatatype)
    (hne : native_streq sP sC = false)
    (BC : SmtDatatype)
    (hBC : BC = __smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC)
    (hInhBC : native_inhabited_type (SmtType.Datatype sC BC) = true)
    (hOld : __smtx_dt_wf_rec (__smtx_dt_substitute sC BC BC) dC = true) :
    GuideTrDt (__smtx_dt_substitute sC BC BC) dC BC := by
  -- the base chain `[(sP, dP)]` satisfies the invariant
  have hOK0 : ChainOK [(sP, dP)] := by
    refine ⟨dP, ?_, hPInh, ?_, ?_⟩
    · simp [chain_ty, __smtx_type_substitute, native_ite, native_streq]
    · simpa [__smtx_type_wf_rec] using hPWf
    · exact fskel_master_dt dP [(sP, dP)]
  -- the top chain is one descent step from it
  have hDesc0 :
      chain_descend [(sP, dP)] sC dC = [(sP, __smtx_dt_lift sC dC dP)] := by
    simp [chain_descend, hne]
  have hTop :
      selfExt [(sP, dP)] sC dC =
        [(sP, __smtx_dt_lift sC dC dP), (sC, BC)] := by
    simp [selfExt, hDesc0, chain_dt, hBC]
  have hNode0 :
      chain_dt (chain_descend [(sP, dP)] sC dC) dC = BC := by
    simp [chain_descend, hne, chain_dt, hBC]
  have hOKTop : ChainOK [(sP, __smtx_dt_lift sC dC dP), (sC, BC)] := by
    rw [← hTop]
    exact chainok_selfExt [(sP, dP)] sC dC sP dP [] rfl hne hOK0
      (by rw [hNode0]; exact hInhBC) (by rw [hNode0]; exact hOld)
  have hFold0 :
      chain_dt [(sP, __smtx_dt_lift sC dC dP), (sC, BC)] dC =
        __smtx_dt_substitute sC BC BC := by
    simp [chain_dt, hBC]
  have hWalk := estab_dt dC sP (__smtx_dt_lift sC dC dP) [(sC, BC)] hOKTop
    (by rw [hFold0]; exact hOld)
  have hFold :
      chain_dt [(sP, __smtx_dt_lift sC dC dP), (sC, BC)] dC =
        __smtx_dt_substitute sC BC BC := by
    simp [chain_dt, hBC]
  rw [hFold, ← hBC] at hWalk
  exact hWalk

/-- Wf-diagonalization: the folded form of a nested datatype field of a
diagonal entry is itself diagonal.  `hFWf` is the field's well-formedness
against its raw guide, which the parent's own diagonal well-formedness
supplies at every nested datatype field. -/
theorem wf_diag_push
    (sP : native_String) (dP : SmtDatatype)
    (hPInh : native_inhabited_type (SmtType.Datatype sP dP) = true)
    (hPWf : __smtx_type_wf_rec (SmtType.Datatype sP dP)
        (SmtType.Datatype sP dP) = true)
    (sC : native_String) (dC : SmtDatatype)
    (hFInh : native_inhabited_type
        (__smtx_type_substitute sP dP (SmtType.Datatype sC dC)) = true)
    (hFWf : __smtx_type_wf_rec
        (__smtx_type_substitute sP dP (SmtType.Datatype sC dC))
        (SmtType.Datatype sC dC) = true) :
    __smtx_type_wf_rec
        (__smtx_type_substitute sP dP (SmtType.Datatype sC dC))
        (__smtx_type_substitute sP dP (SmtType.Datatype sC dC)) = true := by
  cases hs : native_streq sP sC with
  | true =>
      simpa [__smtx_type_substitute, native_ite, hs] using hFWf
  | false =>
      have hSub :
          __smtx_type_substitute sP dP (SmtType.Datatype sC dC) =
            SmtType.Datatype sC
              (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) := by
        simp [__smtx_type_substitute, native_ite, hs]
      rw [hSub] at hFInh hFWf ⊢
      have hOld :
          __smtx_dt_wf_rec
            (__smtx_dt_substitute sC
              (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC)
              (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC))
            dC = true := by
        simpa [__smtx_type_wf_rec] using hFWf
      have hTr := wf_diag_establish sP dP hPInh hPWf sC dC hs
        (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) rfl hFInh hOld
      simpa [__smtx_type_wf_rec] using guideTrDt_wf hTr hOld

end Smtm
