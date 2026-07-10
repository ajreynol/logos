import Cpc.Proofs.Canonical.TypeDefaultBasic
import Cpc.Proofs.Translation.SmtFreeRefs

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

A *substitution chain* is a list of `(name, raw body, payload)` triples applied
innermost-first (head first).  Only the payload participates in substitution;
the raw body is proof-relevant history.  In particular, later lifts can make
two payloads with the same name syntactically different even though both came
from the same name-consistent source body.  Retaining that source is what lets
the invariant distinguish valid rotations from arbitrary same-name aliases.

The folded side of the establishment walk is always the image of the raw
guide under the payload projection of such a chain; `chain_descend` describes
how a chain acts on the body of a `Datatype` node (payloads are lifted against
the evolving body, same-named entries are shielded), exactly mirroring
`__smtx_type_substitute`'s recursion. -/

private abbrev SubstChain :=
  List (native_String × SmtDatatype × SmtDatatype)

/-! `usesHead* t` is the part of free-reference tracking relevant to this
proof.  Containers are opaque to SMT datatype substitution, a same-named
datatype shields its body, and a direct `TypeRef t` consumes the head entry.

This demand predicate is essential: extending an arbitrary `ChainOK` chain is
false.  The establishment walk only needs the head facts in subtrees where a
free `TypeRef t` can actually be reached. -/
mutual
private def usesHeadTy (t : native_String) : SmtType → Bool
  | SmtType.TypeRef r => native_streq t r
  | SmtType.Datatype s d =>
      if native_streq t s = true then false else usesHeadDt t d
  | _ => false
private def usesHeadDtc (t : native_String) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.unit => false
  | SmtDatatypeCons.cons T c => native_or (usesHeadTy t T) (usesHeadDtc t c)
private def usesHeadDt (t : native_String) : SmtDatatype → Bool
  | SmtDatatype.null => false
  | SmtDatatype.sum c d => native_or (usesHeadDtc t c) (usesHeadDt t d)
end

private def chain_ty : SubstChain → SmtType → SmtType
  | [], T => T
  | (s, _R, P) :: ρ, T => chain_ty ρ (__smtx_type_substitute s P T)

private def chain_dtc : SubstChain → SmtDatatypeCons → SmtDatatypeCons
  | [], c => c
  | (s, _R, P) :: ρ, c => chain_dtc ρ (__smtx_dtc_substitute s P c)

private def chain_dt : SubstChain → SmtDatatype → SmtDatatype
  | [], X => X
  | (s, _R, P) :: ρ, X => chain_dt ρ (__smtx_dt_substitute s P X)

private def chain_descend : SubstChain → native_String → SmtDatatype → SubstChain
  | [], _, _ => []
  | (s, R, P) :: ρ, s3, X =>
      if native_streq s s3 = true then chain_descend ρ s3 X
      else (s, R, __smtx_dt_lift s3 X P) ::
        chain_descend ρ s3 (__smtx_dt_substitute s (__smtx_dt_lift s3 X P) X)

private theorem chain_dt_null :
    ∀ ρ : SubstChain, chain_dt ρ SmtDatatype.null = SmtDatatype.null
  | [] => rfl
  | (s, R, P) :: ρ => by
      simp [chain_dt, __smtx_dt_substitute, chain_dt_null ρ]

private theorem chain_dtc_unit :
    ∀ ρ : SubstChain, chain_dtc ρ SmtDatatypeCons.unit = SmtDatatypeCons.unit
  | [] => rfl
  | (s, R, P) :: ρ => by
      simp [chain_dtc, __smtx_dtc_substitute, chain_dtc_unit ρ]

private theorem chain_dt_sum :
    ∀ (ρ : SubstChain) (c : SmtDatatypeCons) (d : SmtDatatype),
      chain_dt ρ (SmtDatatype.sum c d) =
        SmtDatatype.sum (chain_dtc ρ c) (chain_dt ρ d)
  | [], _c, _d => rfl
  | (s, R, P) :: ρ, c, d => by
      simp [chain_dt, chain_dtc, __smtx_dt_substitute, chain_dt_sum ρ]

private theorem chain_dtc_cons :
    ∀ (ρ : SubstChain) (T : SmtType) (c : SmtDatatypeCons),
      chain_dtc ρ (SmtDatatypeCons.cons T c) =
        SmtDatatypeCons.cons (chain_ty ρ T) (chain_dtc ρ c)
  | [], _T, _c => rfl
  | (s, R, P) :: ρ, T, c => by
      simp [chain_dtc, chain_ty, __smtx_dtc_substitute, chain_dtc_cons ρ]

/-- A chain fixes any type it substitutes trivially (containers and base
types). -/
private theorem chain_ty_fix (T : SmtType)
    (hFix : ∀ (s : native_String) (P : SmtDatatype),
      __smtx_type_substitute s P T = T) :
    ∀ ρ : SubstChain, chain_ty ρ T = T
  | [] => rfl
  | (s, R, P) :: ρ => by
      rw [chain_ty, hFix s P, chain_ty_fix T hFix ρ]

/-- How a chain acts on a datatype node: it descends into the body with
lifted payloads. -/
private theorem chain_ty_datatype :
    ∀ (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype),
      chain_ty ρ (SmtType.Datatype s3 X) =
        SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)
  | [], _s3, _X => rfl
  | (s, R, P) :: ρ, s3, X => by
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
    ∀ (ρ : SubstChain) (s : native_String) (R Q X : SmtDatatype),
      chain_dt (ρ ++ [(s, R, Q)]) X = __smtx_dt_substitute s Q (chain_dt ρ X)
  | [], _s, _R, _Q, _X => rfl
  | (s0, R0, P0) :: ρ, s, R, Q, X => by
      simp only [List.cons_append, chain_dt]
      exact chain_dt_append_one ρ s R Q (__smtx_dt_substitute s0 P0 X)

/-- Extend a chain across a descent into `(s3, X)`: the descended chain plus
the resolved body of the node as a final self-entry. -/
private def selfExt (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype) :
    SubstChain :=
  chain_descend ρ s3 X ++ [(s3, X, chain_dt (chain_descend ρ s3 X) X)]

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
          [(s5, HB, chain_dt (chain_descend ρ s5 HB) HB)])
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
                [(b, B0, chain_dt (chain_descend ρF b B0) B0)]) B0) B0 ≠
            SmtValue.NotValue := by
        rw [chain_dt_append_one]
        simpa [__smtx_type_default_rec] using hOld
      have h := defpres_dt B0
        (chain_descend ρF b B0 ++
          [(b, B0, chain_dt (chain_descend ρF b B0) B0)])
        (chain_descend ρN b B0 ++
          [(b, B0, chain_dt (chain_descend ρN b B0) B0)])
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
        (chain_dt [(t, B, B)] B) B ≠ SmtValue.NotValue := by
    simpa [__smtx_type_default, __smtx_type_default_rec, chain_dt]
      using hOldNe
  have hNew := defpres_dt B [(t, B, B)]
    (ρ ++ [(t, B, chain_dt ρ B)]) ρ
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

/-- Substituting into the folded side of an inhabited type cannot destroy its
default constructor.  The datatype case is exactly a one-entry chain image;
all other inhabited type forms are fixed by SMT datatype substitution. -/
private theorem inhabited_type_substitute
    (q : native_String) (Q : SmtDatatype) :
    ∀ T : SmtType,
      native_inhabited_type T = true →
        native_inhabited_type (__smtx_type_substitute q Q T) = true
  | SmtType.Datatype s D, hInh => by
      cases hqs : native_streq q s with
      | true =>
          simpa [__smtx_type_substitute, native_ite, hqs] using hInh
      | false =>
          have hImage := inhabited_chain_image s D
            [(q, Q, __smtx_dt_lift s D Q)] hInh
          simpa [__smtx_type_substitute, native_ite, hqs, chain_dt]
            using hImage
  | SmtType.TypeRef r, hInh => by
      simp [native_inhabited_type, __smtx_type_default,
        __smtx_type_default_rec, __smtx_typeof_value, native_Teq,
        native_not, native_and] at hInh
  | SmtType.None, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Bool, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Int, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Real, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.RegLan, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.BitVec w, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Map A B, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Set A, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Seq A, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.Char, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.USort u, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.FunType A B, hInh => by
      simpa [__smtx_type_substitute] using hInh
  | SmtType.DtcAppType A B, hInh => by
      simpa [__smtx_type_substitute] using hInh

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

/-! Without adding the lifted name to the excuse set, a successful default
path has only two possibilities: the path survives the lift, or it traversed
an exact occurrence of the folded datatype, whose body is therefore itself
defaultable. -/
mutual

private theorem refDef_lift_split_ty (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ T : SmtType, refDefTy S T = true →
      refDefTy S (__smtx_type_lift s X T) = true ∨ refDefDt S X = true
  | SmtType.Datatype q D, h => by
      by_cases hFold : native_Teq
          (SmtType.Datatype s X) (SmtType.Datatype q D) = true
      · have hEq : SmtType.Datatype s X = SmtType.Datatype q D := by
          simpa [native_Teq] using hFold
        cases hEq
        exact Or.inr (by simpa [refDefTy] using h)
      · have hBody : refDefDt S D = true := by simpa [refDefTy] using h
        rcases refDef_lift_split_dt s X S D hBody with hLift | hX
        · exact Or.inl (by
            simp [__smtx_type_lift, native_ite, hFold, refDefTy, hLift])
        · exact Or.inr hX
  | SmtType.TypeRef r, h => Or.inl (by simpa [__smtx_type_lift] using h)
  | SmtType.Map A B, h => Or.inl (by simpa [__smtx_type_lift] using h)
  | SmtType.None, h => by simp [refDefTy] at h
  | SmtType.DtcAppType A B, h => by simp [refDefTy] at h
  | SmtType.Bool, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.Int, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.Real, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.RegLan, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.BitVec w, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.Char, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.Set A, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.Seq A, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.USort u, h => Or.inl (by simp [__smtx_type_lift, refDefTy])
  | SmtType.FunType A B, h => Or.inl (by simp [__smtx_type_lift, refDefTy])

private theorem refDef_lift_split_dtc (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ c : SmtDatatypeCons, refDefDtc S c = true →
      refDefDtc S (__smtx_dtc_lift s X c) = true ∨ refDefDt S X = true
  | SmtDatatypeCons.unit, h => Or.inl (by simp [__smtx_dtc_lift, refDefDtc])
  | SmtDatatypeCons.cons T c, h => by
      have hp : refDefTy S T = true ∧ refDefDtc S c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using h
      rcases refDef_lift_split_ty s X S T hp.1 with hT | hX
      · rcases refDef_lift_split_dtc s X S c hp.2 with hc | hX
        · exact Or.inl (by simp [__smtx_dtc_lift, refDefDtc, hT, hc])
        · exact Or.inr hX
      · exact Or.inr hX

private theorem refDef_lift_split_dt (s : native_String) (X : SmtDatatype)
    (S : RefList) :
    ∀ D : SmtDatatype, refDefDt S D = true →
      refDefDt S (__smtx_dt_lift s X D) = true ∨ refDefDt S X = true
  | SmtDatatype.null, h => by simp [refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp : refDefDtc S c = true ∨ refDefDt S D = true := by
        simpa [refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · rcases refDef_lift_split_dtc s X S c hc with hc' | hX
        · exact Or.inl (by simp [__smtx_dt_lift, refDefDt, hc'])
        · exact Or.inr hX
      · rcases refDef_lift_split_dt s X S D hD with hD' | hX
        · exact Or.inl (by simp [__smtx_dt_lift, refDefDt, hD'])
        · exact Or.inr hX

end

/-! Lifting cannot create an unexcused default path: an exact fold replaces a
datatype node by an unexcused reference, while every other constructor is
preserved recursively. -/
mutual

private theorem refDef_lift_inv_ty (s : native_String) (X : SmtDatatype) :
    ∀ T : SmtType,
      refDefTy native_reflist_nil (__smtx_type_lift s X T) = true →
        refDefTy native_reflist_nil T = true
  | SmtType.Datatype q D, h => by
      by_cases hFold : native_Teq
          (SmtType.Datatype s X) (SmtType.Datatype q D) = true
      · simp [__smtx_type_lift, native_ite, hFold, refDefTy,
          native_reflist_contains, native_reflist_nil] at h
      · have hBody :
            refDefDt native_reflist_nil (__smtx_dt_lift s X D) = true := by
          simpa [__smtx_type_lift, native_ite, hFold, refDefTy] using h
        simpa [refDefTy] using refDef_lift_inv_dt s X D hBody
  | SmtType.TypeRef r, h => by simpa [__smtx_type_lift] using h
  | SmtType.Map A B, h => by simpa [__smtx_type_lift] using h
  | SmtType.None, h => by simpa [__smtx_type_lift] using h
  | SmtType.Bool, h => by simpa [__smtx_type_lift] using h
  | SmtType.Int, h => by simpa [__smtx_type_lift] using h
  | SmtType.Real, h => by simpa [__smtx_type_lift] using h
  | SmtType.RegLan, h => by simpa [__smtx_type_lift] using h
  | SmtType.BitVec w, h => by simpa [__smtx_type_lift] using h
  | SmtType.Set A, h => by simpa [__smtx_type_lift] using h
  | SmtType.Seq A, h => by simpa [__smtx_type_lift] using h
  | SmtType.Char, h => by simpa [__smtx_type_lift] using h
  | SmtType.USort u, h => by simpa [__smtx_type_lift] using h
  | SmtType.FunType A B, h => by simpa [__smtx_type_lift] using h
  | SmtType.DtcAppType A B, h => by simpa [__smtx_type_lift] using h

private theorem refDef_lift_inv_dtc (s : native_String) (X : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      refDefDtc native_reflist_nil (__smtx_dtc_lift s X c) = true →
        refDefDtc native_reflist_nil c = true
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_lift, refDefDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp :
          refDefTy native_reflist_nil (__smtx_type_lift s X T) = true ∧
            refDefDtc native_reflist_nil (__smtx_dtc_lift s X c) = true := by
        simpa [__smtx_dtc_lift, refDefDtc, Bool.and_eq_true] using h
      simp [refDefDtc, Bool.and_eq_true,
        refDef_lift_inv_ty s X T hp.1,
        refDef_lift_inv_dtc s X c hp.2]

private theorem refDef_lift_inv_dt (s : native_String) (X : SmtDatatype) :
    ∀ D : SmtDatatype,
      refDefDt native_reflist_nil (__smtx_dt_lift s X D) = true →
        refDefDt native_reflist_nil D = true
  | SmtDatatype.null, h => by simp [__smtx_dt_lift, refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp :
          refDefDtc native_reflist_nil (__smtx_dtc_lift s X c) = true ∨
            refDefDt native_reflist_nil (__smtx_dt_lift s X D) = true := by
        simpa [__smtx_dt_lift, refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · simp [refDefDt, Bool.or_eq_true,
          refDef_lift_inv_dtc s X c hc]
      · simp [refDefDt, Bool.or_eq_true,
          refDef_lift_inv_dt s X D hD]

end

/-! Substitution cannot destroy an unexcused default path: such a path never
uses a `TypeRef`, which is the only form substitution replaces. -/
mutual

private theorem refDef_subst_empty_ty (s : native_String) (K : SmtDatatype) :
    ∀ T : SmtType, refDefTy native_reflist_nil T = true →
      refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true
  | SmtType.TypeRef r, h => by
      simp [refDefTy, native_reflist_contains, native_reflist_nil] at h
  | SmtType.Datatype q D, h => by
      have hD : refDefDt native_reflist_nil D = true := by
        simpa [refDefTy] using h
      cases hsq : native_streq s q with
      | true => simpa [__smtx_type_substitute, native_ite, hsq, refDefTy] using hD
      | false =>
          simp [__smtx_type_substitute, native_ite, hsq, refDefTy,
            refDef_subst_empty_dt s (__smtx_dt_lift q D K) D hD]
  | SmtType.Map A B, h => by simpa [__smtx_type_substitute] using h
  | SmtType.None, h => by simp [refDefTy] at h
  | SmtType.DtcAppType A B, h => by simp [refDefTy] at h
  | SmtType.Bool, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Int, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Real, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.RegLan, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.BitVec w, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Char, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Set A, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Seq A, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.USort u, h => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.FunType A B, h => by simp [__smtx_type_substitute, refDefTy]

private theorem refDef_subst_empty_dtc (s : native_String) (K : SmtDatatype) :
    ∀ c : SmtDatatypeCons, refDefDtc native_reflist_nil c = true →
      refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_substitute, refDefDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp : refDefTy native_reflist_nil T = true ∧
          refDefDtc native_reflist_nil c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using h
      simp [__smtx_dtc_substitute, refDefDtc,
        refDef_subst_empty_ty s K T hp.1,
        refDef_subst_empty_dtc s K c hp.2]

private theorem refDef_subst_empty_dt (s : native_String) (K : SmtDatatype) :
    ∀ D : SmtDatatype, refDefDt native_reflist_nil D = true →
      refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true
  | SmtDatatype.null, h => by simp [refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp : refDefDtc native_reflist_nil c = true ∨
          refDefDt native_reflist_nil D = true := by
        simpa [refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · simp [__smtx_dt_substitute, refDefDt,
          refDef_subst_empty_dtc s K c hc]
      · simp [__smtx_dt_substitute, refDefDt,
          refDef_subst_empty_dt s K D hD]

end

/-! Conversely, a successful default path after substitution came either
from the original syntax or from the substituted payload.  This path-sensitive
split is what lets the confluence proof peel an old chain without assuming
that every suffix payload is independently inhabited. -/
mutual

private theorem refDef_subst_split_ty (s : native_String) (K : SmtDatatype) :
    ∀ T : SmtType,
      refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true →
        refDefTy native_reflist_nil T = true ∨
          refDefDt native_reflist_nil K = true
  | SmtType.TypeRef r, h => by
      cases hsr : native_streq s r with
      | true =>
          exact Or.inr (by
            simpa [__smtx_type_substitute, native_ite, hsr, refDefTy] using h)
      | false =>
          simp [__smtx_type_substitute, native_ite, hsr, refDefTy,
            native_reflist_contains, native_reflist_nil] at h
  | SmtType.Datatype q D, h => by
      cases hsq : native_streq s q with
      | true =>
          exact Or.inl (by
            simpa [__smtx_type_substitute, native_ite, hsq] using h)
      | false =>
          have hBody :
              refDefDt native_reflist_nil
                (__smtx_dt_substitute s (__smtx_dt_lift q D K) D) = true := by
            simpa [__smtx_type_substitute, native_ite, hsq, refDefTy] using h
          rcases refDef_subst_split_dt s (__smtx_dt_lift q D K) D hBody
            with hD | hLift
          · exact Or.inl (by simpa [refDefTy] using hD)
          · exact Or.inr (refDef_lift_inv_dt q D K hLift)
  | SmtType.Map A B, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.None, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Bool, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Int, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Real, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.RegLan, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.BitVec w, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Set A, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Seq A, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.Char, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.USort u, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.FunType A B, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)
  | SmtType.DtcAppType A B, h => Or.inl (by
      simpa [__smtx_type_substitute] using h)

private theorem refDef_subst_split_dtc (s : native_String) (K : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true →
        refDefDtc native_reflist_nil c = true ∨
          refDefDt native_reflist_nil K = true
  | SmtDatatypeCons.unit, h => Or.inl (by
      simp [refDefDtc])
  | SmtDatatypeCons.cons T c, h => by
      have hp :
          refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true ∧
            refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true := by
        simpa [__smtx_dtc_substitute, refDefDtc, Bool.and_eq_true] using h
      rcases refDef_subst_split_ty s K T hp.1 with hT | hK
      · rcases refDef_subst_split_dtc s K c hp.2 with hc | hK
        · exact Or.inl (by simp [refDefDtc, hT, hc])
        · exact Or.inr hK
      · exact Or.inr hK

private theorem refDef_subst_split_dt (s : native_String) (K : SmtDatatype) :
    ∀ D : SmtDatatype,
      refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true →
        refDefDt native_reflist_nil D = true ∨
          refDefDt native_reflist_nil K = true
  | SmtDatatype.null, h => by simp [__smtx_dt_substitute, refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp :
          refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true ∨
            refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true := by
        simpa [__smtx_dt_substitute, refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · rcases refDef_subst_split_dtc s K c hc with hc' | hK
        · exact Or.inl (by simp [refDefDt, hc'])
        · exact Or.inr hK
      · rcases refDef_subst_split_dt s K D hD with hD' | hK
        · exact Or.inl (by simp [refDefDt, hD'])
        · exact Or.inr hK

end

/-! Defaultability is monotone in a substitution payload.  The datatype case
needs care because the payload is lifted under a nested binder: if that lift
loses the chosen path, `refDef_lift_split_dt` says the binder body itself has
the replacement path, so substitution succeeds without using the payload. -/
mutual

private theorem refDef_subst_congr_ty
    (s : native_String) (K L : SmtDatatype)
    (hKL : refDefDt native_reflist_nil K = true →
      refDefDt native_reflist_nil L = true) :
    ∀ T : SmtType,
      refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true →
        refDefTy native_reflist_nil (__smtx_type_substitute s L T) = true
  | SmtType.TypeRef r, h => by
      cases hsr : native_streq s r with
      | true =>
          have hK : refDefDt native_reflist_nil K = true := by
            simpa [__smtx_type_substitute, native_ite, hsr, refDefTy] using h
          simpa [__smtx_type_substitute, native_ite, hsr, refDefTy] using hKL hK
      | false =>
          simpa [__smtx_type_substitute, native_ite, hsr] using h
  | SmtType.Datatype q D, h => by
      cases hsq : native_streq s q with
      | true =>
          simpa [__smtx_type_substitute, native_ite, hsq] using h
      | false =>
          have hBody :
              refDefDt native_reflist_nil
                (__smtx_dt_substitute s (__smtx_dt_lift q D K) D) = true := by
            simpa [__smtx_type_substitute, native_ite, hsq, refDefTy] using h
          by_cases hLiftK :
              refDefDt native_reflist_nil (__smtx_dt_lift q D K) = true
          · have hL : refDefDt native_reflist_nil L = true :=
              hKL (refDef_lift_inv_dt q D K hLiftK)
            rcases refDef_lift_split_dt q D native_reflist_nil L hL with
              hLiftL | hD
            · have hNew := refDef_subst_congr_dt s
                (__smtx_dt_lift q D K) (__smtx_dt_lift q D L)
                (fun _ => hLiftL) D hBody
              simpa [__smtx_type_substitute, native_ite, hsq, refDefTy]
                using hNew
            · have hNew := refDef_subst_empty_dt s (__smtx_dt_lift q D L)
                D hD
              simpa [__smtx_type_substitute, native_ite, hsq, refDefTy]
                using hNew
          · rcases refDef_subst_split_dt s (__smtx_dt_lift q D K) D hBody
              with hD | hBad
            · have hNew := refDef_subst_empty_dt s (__smtx_dt_lift q D L)
                D hD
              simpa [__smtx_type_substitute, native_ite, hsq, refDefTy]
                using hNew
            · exact absurd hBad hLiftK
  | SmtType.Map A B, h => by simpa [__smtx_type_substitute] using h
  | SmtType.None, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Bool, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Int, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Real, h => by simpa [__smtx_type_substitute] using h
  | SmtType.RegLan, h => by simpa [__smtx_type_substitute] using h
  | SmtType.BitVec w, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Set A, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Seq A, h => by simpa [__smtx_type_substitute] using h
  | SmtType.Char, h => by simpa [__smtx_type_substitute] using h
  | SmtType.USort u, h => by simpa [__smtx_type_substitute] using h
  | SmtType.FunType A B, h => by simpa [__smtx_type_substitute] using h
  | SmtType.DtcAppType A B, h => by simpa [__smtx_type_substitute] using h

private theorem refDef_subst_congr_dtc
    (s : native_String) (K L : SmtDatatype)
    (hKL : refDefDt native_reflist_nil K = true →
      refDefDt native_reflist_nil L = true) :
    ∀ c : SmtDatatypeCons,
      refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true →
        refDefDtc native_reflist_nil (__smtx_dtc_substitute s L c) = true
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_substitute, refDefDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp :
          refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true ∧
            refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true := by
        simpa [__smtx_dtc_substitute, refDefDtc, Bool.and_eq_true] using h
      simp [__smtx_dtc_substitute, refDefDtc, Bool.and_eq_true,
        refDef_subst_congr_ty s K L hKL T hp.1,
        refDef_subst_congr_dtc s K L hKL c hp.2]

private theorem refDef_subst_congr_dt
    (s : native_String) (K L : SmtDatatype)
    (hKL : refDefDt native_reflist_nil K = true →
      refDefDt native_reflist_nil L = true) :
    ∀ D : SmtDatatype,
      refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true →
        refDefDt native_reflist_nil (__smtx_dt_substitute s L D) = true
  | SmtDatatype.null, h => by simp [__smtx_dt_substitute, refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp :
          refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true ∨
            refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true := by
        simpa [__smtx_dt_substitute, refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · simp [__smtx_dt_substitute, refDefDt, Bool.or_eq_true,
          refDef_subst_congr_dtc s K L hKL c hc]
      · simp [__smtx_dt_substitute, refDefDt, Bool.or_eq_true,
          refDef_subst_congr_dt s K L hKL D hD]

end

/-! Resolving the one excused name with a defaultable payload produces an
unexcused default path.  `noDt*` prevents a same-named datatype binder from
shielding an introduced reference. -/
mutual

private theorem refDef_resolve_ty (s : native_String) :
    ∀ (T : SmtType) (K : SmtDatatype),
      noDtTy s T = true →
      refDefTy (native_reflist_insert native_reflist_nil s) T = true →
      refDefDt native_reflist_nil K = true →
      refDefTy native_reflist_nil (__smtx_type_substitute s K T) = true
  | SmtType.TypeRef r, K, _hNoDt, hRef, hK => by
      have hrs : r = s := by
        simpa [refDefTy, native_reflist_contains, native_reflist_insert,
          native_reflist_nil] using hRef
      subst r
      simp [__smtx_type_substitute, native_ite, native_streq, refDefTy, hK]
  | SmtType.Datatype q D, K, hNoDt, hRef, hK => by
      have hn : native_streq q s = false ∧ noDtDt s D = true := by
        simpa [noDtTy, native_and, native_not, Bool.and_eq_true] using hNoDt
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hn.1
      have hD :
          refDefDt (native_reflist_insert native_reflist_nil s) D = true := by
        simpa [refDefTy] using hRef
      rcases refDef_lift_split_dt q D native_reflist_nil K hK with hK' | hBody
      · simp [__smtx_type_substitute, native_ite, hsq, refDefTy,
          refDef_resolve_dt s D (__smtx_dt_lift q D K) hn.2 hD hK']
      · simp [__smtx_type_substitute, native_ite, hsq, refDefTy,
          refDef_subst_empty_dt s (__smtx_dt_lift q D K) D hBody]
  | SmtType.Map A B, K, _hNoDt, hRef, _hK => by
      simpa [__smtx_type_substitute] using hRef
  | SmtType.None, K, _hNoDt, hRef, _hK => by simp [refDefTy] at hRef
  | SmtType.DtcAppType A B, K, _hNoDt, hRef, _hK => by simp [refDefTy] at hRef
  | SmtType.Bool, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Int, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Real, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.RegLan, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.BitVec w, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Char, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Set A, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.Seq A, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.USort u, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]
  | SmtType.FunType A B, K, _hNoDt, hRef, _hK => by simp [__smtx_type_substitute, refDefTy]

private theorem refDef_resolve_dtc (s : native_String) :
    ∀ (c : SmtDatatypeCons) (K : SmtDatatype),
      noDtDtc s c = true →
      refDefDtc (native_reflist_insert native_reflist_nil s) c = true →
      refDefDt native_reflist_nil K = true →
      refDefDtc native_reflist_nil (__smtx_dtc_substitute s K c) = true
  | SmtDatatypeCons.unit, K, _hNoDt, _hRef, _hK => by
      simp [__smtx_dtc_substitute, refDefDtc]
  | SmtDatatypeCons.cons T c, K, hNoDt, hRef, hK => by
      have hn : noDtTy s T = true ∧ noDtDtc s c = true := by
        simpa [noDtDtc, native_and, Bool.and_eq_true] using hNoDt
      have hr : refDefTy (native_reflist_insert native_reflist_nil s) T = true ∧
          refDefDtc (native_reflist_insert native_reflist_nil s) c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using hRef
      simp [__smtx_dtc_substitute, refDefDtc,
        refDef_resolve_ty s T K hn.1 hr.1 hK,
        refDef_resolve_dtc s c K hn.2 hr.2 hK]

private theorem refDef_resolve_dt (s : native_String) :
    ∀ (D : SmtDatatype) (K : SmtDatatype),
      noDtDt s D = true →
      refDefDt (native_reflist_insert native_reflist_nil s) D = true →
      refDefDt native_reflist_nil K = true →
      refDefDt native_reflist_nil (__smtx_dt_substitute s K D) = true
  | SmtDatatype.null, K, _hNoDt, hRef, _hK => by simp [refDefDt] at hRef
  | SmtDatatype.sum c D, K, hNoDt, hRef, hK => by
      have hn : noDtDtc s c = true ∧ noDtDt s D = true := by
        simpa [noDtDt, native_and, Bool.and_eq_true] using hNoDt
      have hr : refDefDtc (native_reflist_insert native_reflist_nil s) c = true ∨
          refDefDt (native_reflist_insert native_reflist_nil s) D = true := by
        simpa [refDefDt, Bool.or_eq_true] using hRef
      rcases hr with hc | hD
      · simp [__smtx_dt_substitute, refDefDt,
          refDef_resolve_dtc s c K hn.1 hc hK]
      · simp [__smtx_dt_substitute, refDefDt,
          refDef_resolve_dt s D K hn.2 hD hK]

end

/-! If every occurrence of a datatype name has exactly the body being
folded, the lift removes all datatype nodes with that name. -/
mutual

private theorem noDt_lift_of_noStray_ty (s : native_String) (X : SmtDatatype) :
    ∀ T : SmtType, noStrayTy s X T = true →
      noDtTy s (__smtx_type_lift s X T) = true
  | SmtType.Datatype q D, h => by
      by_cases hFold : native_Teq
          (SmtType.Datatype s X) (SmtType.Datatype q D) = true
      · simp [__smtx_type_lift, native_ite, hFold, noDtTy]
      · have hp : native_streq q s = false ∧ noStrayDt s X D = true := by
          simp only [noStrayTy, native_ite, if_neg hFold, native_and,
            native_not, Bool.and_eq_true] at h
          constructor
          · cases hqs : native_streq q s <;> simp_all [native_not]
          · exact h.2
        simp [__smtx_type_lift, native_ite, hFold, noDtTy, native_and,
          native_not, hp.1, noDt_lift_of_noStray_dt s X D hp.2]
  | SmtType.TypeRef r, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.None, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Bool, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Int, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Real, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.RegLan, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.BitVec w, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Map A B, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Set A, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Seq A, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.Char, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.USort u, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.FunType A B, h => by simp [__smtx_type_lift, noDtTy]
  | SmtType.DtcAppType A B, h => by simp [__smtx_type_lift, noDtTy]

private theorem noDt_lift_of_noStray_dtc (s : native_String) (X : SmtDatatype) :
    ∀ c : SmtDatatypeCons, noStrayDtc s X c = true →
      noDtDtc s (__smtx_dtc_lift s X c) = true
  | SmtDatatypeCons.unit, h => by simp [__smtx_dtc_lift, noDtDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp : noStrayTy s X T = true ∧ noStrayDtc s X c = true := by
        simpa [noStrayDtc, native_and, Bool.and_eq_true] using h
      simp [__smtx_dtc_lift, noDtDtc, native_and,
        noDt_lift_of_noStray_ty s X T hp.1,
        noDt_lift_of_noStray_dtc s X c hp.2]

private theorem noDt_lift_of_noStray_dt (s : native_String) (X : SmtDatatype) :
    ∀ D : SmtDatatype, noStrayDt s X D = true →
      noDtDt s (__smtx_dt_lift s X D) = true
  | SmtDatatype.null, h => by simp [__smtx_dt_lift, noDtDt]
  | SmtDatatype.sum c D, h => by
      have hp : noStrayDtc s X c = true ∧ noStrayDt s X D = true := by
        simpa [noStrayDt, native_and, Bool.and_eq_true] using h
      simp [__smtx_dt_lift, noDtDt, native_and,
        noDt_lift_of_noStray_dtc s X c hp.1,
        noDt_lift_of_noStray_dt s X D hp.2]

end

/-- Defaultability is preserved by reversing one edge between two inhabited
datatype bodies.  `noStray` is the essential alias condition: without it, a
mismatched same-name binder can shield a reference introduced by the lift. -/
private theorem refDef_edge_rotate
    (t s : native_String) (D X B : SmtDatatype)
    (hD : refDefDt native_reflist_nil D = true)
    (hB : refDefDt native_reflist_nil B = true)
    (hNoStray : noStrayDt s X D = true) :
    refDefDt native_reflist_nil
      (__smtx_dt_substitute s
        (__smtx_dt_lift t (__smtx_dt_lift s X D) B)
        (__smtx_dt_lift s X D)) = true := by
  let L := __smtx_dt_lift s X D
  let K := __smtx_dt_lift t L B
  have hExcused :
      refDefDt (native_reflist_insert native_reflist_nil s) L = true := by
    exact refDef_lift_dt s X native_reflist_nil D hD
  have hNoDt : noDtDt s L = true := by
    exact noDt_lift_of_noStray_dt s X D hNoStray
  rcases refDef_lift_split_dt t L native_reflist_nil B hB with hK | hL
  · exact refDef_resolve_dt s L K hNoDt hExcused hK
  · exact refDef_subst_empty_dt s K L hL

/-! On an empty excuse set, `refDef*` is not merely an abstraction: it
constructs a real non-`NotValue` default for every substitution-related
folded side. -/
mutual

private theorem default_ne_of_refDef_ty :
    ∀ {V T : SmtType}, SubstStar V T →
      refDefTy native_reflist_nil T = true →
      __smtx_type_default_rec V T ≠ SmtValue.NotValue
  | _, _, SubstStar.refl (SmtType.TypeRef r), h => by
      simp [refDefTy, native_reflist_contains, native_reflist_nil] at h
  | _, _, SubstStar.refl (SmtType.Datatype s D), h => by
      have hD : refDefDt native_reflist_nil D = true := by
        simpa [refDefTy] using h
      simpa [__smtx_type_default_rec] using
        default_ne_of_refDef_dt (dtSubstStar_of_subst s D D) hD
          s D native_nat_zero
  | _, _, SubstStar.refl SmtType.None, h => by simp [refDefTy] at h
  | _, _, SubstStar.refl (SmtType.DtcAppType A B), h => by simp [refDefTy] at h
  | _, _, SubstStar.refl (SmtType.Map A B), h => by
      have hB : native_not
          (native_veq (__smtx_type_default_rec B B) SmtValue.NotValue) = true := by
        simpa [refDefTy] using h
      cases hb : native_veq (__smtx_type_default_rec B B) SmtValue.NotValue <;>
        simp_all [__smtx_type_default_rec, native_ite, native_not]
  | _, _, SubstStar.refl SmtType.Bool, h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl SmtType.Int, h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl SmtType.Real, h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl SmtType.RegLan, h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl (SmtType.BitVec w), h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl SmtType.Char, h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl (SmtType.Set A), h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl (SmtType.Seq A), h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl (SmtType.USort u), h => by simp [__smtx_type_default_rec]
  | _, _, SubstStar.refl (SmtType.FunType A B), h => by
      simp [__smtx_type_default_rec]
  | _, _, @SubstStar.dt sF sU dF dU hRel, h => by
      have hD : refDefDt native_reflist_nil dU = true := by
        simpa [refDefTy] using h
      simpa [__smtx_type_default_rec] using
        default_ne_of_refDef_dt (dtSubstStar_subst sF dF hRel) hD
          sF dF native_nat_zero

private theorem default_ne_of_refDef_field
    {TF TU : SmtType} (hRel : FieldRel TF TU)
    (hRef : refDefTy native_reflist_nil TU = true) :
    __smtx_type_default_rec TF TU ≠ SmtValue.NotValue := by
  cases hRel with
  | rel h => exact default_ne_of_refDef_ty h hRef
  | forcesNV hNV =>
      have hDiag := default_ne_of_refDef_ty (SubstStar.refl TU) hRef
      exact False.elim (hDiag (hNV TU))

private theorem default_ne_of_refDef_dtc :
    ∀ {cF cU : SmtDatatypeCons}, DtcSubstStar cF cU →
      refDefDtc native_reflist_nil cU = true →
      ∀ v : SmtValue, v ≠ SmtValue.NotValue →
        __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue
  | _, _, DtcSubstStar.unit, hRef, v, hv => by
      simpa [__smtx_datatype_cons_default] using hv
  | _, _, @DtcSubstStar.cons TF TU cF cU hField hTail, hRef, v, hv => by
      have hp : refDefTy native_reflist_nil TU = true ∧
          refDefDtc native_reflist_nil cU = true := by
        simpa [refDefDtc, Bool.and_eq_true] using hRef
      have hHead := default_ne_of_refDef_field hField hp.1
      have hVeq : native_veq (__smtx_type_default_rec TF TU)
          SmtValue.NotValue = false := by
        simpa [native_veq] using hHead
      rw [__smtx_datatype_cons_default, native_ite, if_neg (by simp [hVeq])]
      exact default_ne_of_refDef_dtc hTail hp.2
        (SmtValue.Apply v (__smtx_type_default_rec TF TU)) (by intro h; cases h)

private theorem default_ne_of_refDef_dt :
    ∀ {DF DU : SmtDatatype}, DtSubstStar DF DU →
      refDefDt native_reflist_nil DU = true →
      ∀ (s : native_String) (d : SmtDatatype) (n : native_Nat),
        __smtx_datatype_default s d n DF DU ≠ SmtValue.NotValue
  | _, _, DtSubstStar.null, hRef, s, d, n => by simp [refDefDt] at hRef
  | _, _, @DtSubstStar.sum cF cU DF DU hHead hTail, hRef, s, d, n => by
      have hp : refDefDtc native_reflist_nil cU = true ∨
          refDefDt native_reflist_nil DU = true := by
        simpa [refDefDt, Bool.or_eq_true] using hRef
      rcases hp with hc | hD
      · have hCons := default_ne_of_refDef_dtc hHead hc
          (SmtValue.DtCons s d n) (by intro h; cases h)
        have hVeq : native_veq
            (__smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU)
            SmtValue.NotValue = false := by
          simpa [native_veq] using hCons
        rw [__smtx_datatype_default, native_ite,
          if_pos (by simp [native_not, hVeq])]
        exact hCons
      · by_cases hCons :
          __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU =
            SmtValue.NotValue
        · rw [__smtx_datatype_default, native_ite,
            if_neg (by simp [native_not, native_veq, hCons])]
          exact default_ne_of_refDef_dt hTail hD s d (native_nat_succ n)
        · have hVeq : native_veq
              (__smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU)
              SmtValue.NotValue = false := by
            simpa [native_veq] using hCons
          rw [__smtx_datatype_default, native_ite,
            if_pos (by simp [native_not, hVeq])]
          exact hCons

end

private theorem refDef_empty_of_inhabited
    (s : native_String) (D : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s D) = true) :
    refDefDt native_reflist_nil D = true := by
  have hNe : __smtx_type_default (SmtType.Datatype s D) ≠ SmtValue.NotValue := by
    intro hEq
    have hTy :
        native_Teq
          (__smtx_typeof_value (__smtx_type_default (SmtType.Datatype s D)))
          (SmtType.Datatype s D) = true := by
      simpa [native_inhabited_type, native_and, native_not, native_Teq]
        using hInh
    rw [hEq] at hTy
    simp [__smtx_typeof_value, native_Teq] at hTy
  have hBody :
      __smtx_datatype_default s D native_nat_zero
        (__smtx_dt_substitute s D D) D ≠ SmtValue.NotValue := by
    simpa [__smtx_type_default, __smtx_type_default_rec] using hNe
  exact refDef_of_default_dt native_reflist_nil D
    (__smtx_dt_substitute s D D) s D native_nat_zero hBody

private theorem inhabited_of_refDef_empty
    (s : native_String) (D : SmtDatatype)
    (hRef : refDefDt native_reflist_nil D = true) :
    native_inhabited_type (SmtType.Datatype s D) = true := by
  have hNe : __smtx_type_default (SmtType.Datatype s D) ≠ SmtValue.NotValue := by
    simpa [__smtx_type_default] using
      default_ne_of_refDef_ty (SubstStar.refl (SmtType.Datatype s D))
        (by simpa [refDefTy] using hRef)
  rcases type_default_notvalue_or_typed (SmtType.Datatype s D) with h | h
  · exact absurd h hNe
  · simp [native_inhabited_type, native_and, native_not, native_Teq, h]

private theorem inhabited_edge_rotate
    (t s : native_String) (D X B : SmtDatatype)
    (hD : native_inhabited_type (SmtType.Datatype t D) = true)
    (hB : native_inhabited_type (SmtType.Datatype s B) = true)
    (hNoStray : noStrayDt s X D = true) :
    native_inhabited_type
      (SmtType.Datatype t
        (__smtx_dt_substitute s
          (__smtx_dt_lift t (__smtx_dt_lift s X D) B)
          (__smtx_dt_lift s X D))) = true := by
  exact inhabited_of_refDef_empty t _
    (refDef_edge_rotate t s D X B
      (refDef_empty_of_inhabited t D hD)
      (refDef_empty_of_inhabited s B hB) hNoStray)

/-! ## The chain invariant and the establishment walk -/

/-- Reconstruct the head payload from its raw body and the raw binders kept
in the suffix.  Closed payloads in the suffix deliberately do not participate:
they are results of the closure walk, while this function records only the
sequence of source-level folds. -/
private def liftSources : SubstChain → SmtDatatype → SmtDatatype
  | [], R => R
  | (s, X, _P) :: REST, R =>
      liftSources REST (__smtx_dt_lift s X R)

private def chainHasName (q : native_String) : SubstChain → Bool
  | [] => false
  | (s, _R, _P) :: REST =>
      native_or (native_streq q s) (chainHasName q REST)

/-- Every raw binder recorded in a suffix is an occurrence consistent with
the fixed raw root. -/
private def RawSuffixCons (root : SmtDatatype) : SubstChain → Prop
  | [] => True
  | (s, X, _P) :: REST =>
      __smtx_type_names_consistent_rec root (SmtType.Datatype s X) = true ∧
        RawSuffixCons root REST

private theorem chainHasName_false_parts
    (q s : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (h : chainHasName q ((s, R, P) :: REST) = false) :
    native_streq q s = false ∧ chainHasName q REST = false := by
  simpa [chainHasName, native_or, Bool.or_eq_false_iff] using h

private theorem liftSources_append_one
    (REST : SubstChain) (s : native_String) (X P R : SmtDatatype) :
    liftSources (REST ++ [(s, X, P)]) R =
      __smtx_dt_lift s X (liftSources REST R) := by
  induction REST generalizing R with
  | nil => rfl
  | cons e REST ih =>
      rcases e with ⟨s0, X0, P0⟩
      simp [liftSources, ih]

private theorem liftSources_descend_of_fresh
    (q : native_String) :
    ∀ (REST : SubstChain) (X R : SmtDatatype),
      chainHasName q REST = false →
      liftSources (chain_descend REST q X) R = liftSources REST R
  | [], X, R, _ => rfl
  | (s, R0, P0) :: REST, X, R, hFresh => by
      have hp := chainHasName_false_parts q s R0 P0 REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hp.1
      simp [chain_descend, hsq, liftSources,
        liftSources_descend_of_fresh q REST
          (__smtx_dt_substitute s (__smtx_dt_lift q X P0) X)
          (__smtx_dt_lift s R0 R) hp.2]

private theorem RawSuffixCons_descend
    (root : SmtDatatype) :
    ∀ (REST : SubstChain) (q : native_String) (X : SmtDatatype),
      RawSuffixCons root REST →
      RawSuffixCons root (chain_descend REST q X)
  | [], q, X, _ => trivial
  | (s, R, P) :: REST, q, X, hCons => by
      rcases hCons with ⟨hHead, hTail⟩
      cases hsq : native_streq s q with
      | true =>
          simpa [chain_descend, hsq] using
            RawSuffixCons_descend root REST q X hTail
      | false =>
          simp only [chain_descend, hsq, if_false]
          exact ⟨hHead,
            RawSuffixCons_descend root REST q
              (__smtx_dt_substitute s (__smtx_dt_lift q X P) X) hTail⟩

private theorem RawSuffixCons_append
    (root : SmtDatatype) (REST : SubstChain)
    (s : native_String) (X P : SmtDatatype)
    (hREST : RawSuffixCons root REST)
    (hField : __smtx_type_names_consistent_rec root
      (SmtType.Datatype s X) = true) :
    RawSuffixCons root (REST ++ [(s, X, P)]) := by
  induction REST with
  | nil => exact ⟨hField, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s0, X0, P0⟩
      rcases hREST with ⟨hHead, hTail⟩
      exact ⟨hHead, ih hTail⟩

private def ChainSourceOK (t : native_String) (R P : SmtDatatype)
    (REST : SubstChain) : Prop :=
  P = liftSources REST R ∧
    __smtx_type_names_consistent (SmtType.Datatype t R) = true ∧
      RawSuffixCons R REST

private theorem ChainSourceOK_descend
    (t q : native_String) (R P X Y B : SmtDatatype)
    (REST : SubstChain)
    (hSource : ChainSourceOK t R P REST)
    (hFresh : chainHasName q REST = false)
    (hField : __smtx_type_names_consistent_rec R
      (SmtType.Datatype q X) = true) :
    ChainSourceOK t R (__smtx_dt_lift q X P)
      (chain_descend REST q Y ++ [(q, X, B)]) := by
  rcases hSource with ⟨hPayload, hRoot, hREST⟩
  refine ⟨?_, hRoot, ?_⟩
  · rw [liftSources_append_one,
      liftSources_descend_of_fresh q REST Y R hFresh, ← hPayload]
  · exact RawSuffixCons_append R (chain_descend REST q Y) q X B
      (RawSuffixCons_descend R REST q Y hREST) hField

private def ChainNoDtTy : SubstChain → SmtType → Prop
  | [], _ => True
  | (s, _R, _P) :: REST, T =>
      noDtTy s T = true ∧ ChainNoDtTy REST T

private def ChainNoDtDtc : SubstChain → SmtDatatypeCons → Prop
  | [], _ => True
  | (s, _R, _P) :: REST, c =>
      noDtDtc s c = true ∧ ChainNoDtDtc REST c

private def ChainNoDtDt : SubstChain → SmtDatatype → Prop
  | [], _ => True
  | (s, _R, _P) :: REST, d =>
      noDtDt s d = true ∧ ChainNoDtDt REST d

private theorem ChainNoDtTy_datatype_parts
    (REST : SubstChain) (q : native_String) (X : SmtDatatype)
    (h : ChainNoDtTy REST (SmtType.Datatype q X)) :
    chainHasName q REST = false ∧ ChainNoDtDt REST X := by
  induction REST with
  | nil => exact ⟨rfl, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s, R, P⟩
      rcases h with ⟨hHead, hTail⟩
      have hp : native_streq q s = false ∧ noDtDt s X = true := by
        simpa [noDtTy, native_and, native_not, Bool.and_eq_true] using hHead
      have hRec := ih hTail
      constructor
      · simp [chainHasName, native_or, hp.1, hRec.1]
      · exact ⟨hp.2, hRec.2⟩

private theorem ChainNoDtDtc_parts
    (REST : SubstChain) (T : SmtType) (c : SmtDatatypeCons)
    (h : ChainNoDtDtc REST (SmtDatatypeCons.cons T c)) :
    ChainNoDtTy REST T ∧ ChainNoDtDtc REST c := by
  induction REST with
  | nil => exact ⟨trivial, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s, R, P⟩
      rcases h with ⟨hHead, hTail⟩
      have hp : noDtTy s T = true ∧ noDtDtc s c = true := by
        simpa [noDtDtc, native_and, Bool.and_eq_true] using hHead
      have hRec := ih hTail
      exact ⟨⟨hp.1, hRec.1⟩, ⟨hp.2, hRec.2⟩⟩

private theorem ChainNoDtDt_parts
    (REST : SubstChain) (c : SmtDatatypeCons) (d : SmtDatatype)
    (h : ChainNoDtDt REST (SmtDatatype.sum c d)) :
    ChainNoDtDtc REST c ∧ ChainNoDtDt REST d := by
  induction REST with
  | nil => exact ⟨trivial, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s, R, P⟩
      rcases h with ⟨hHead, hTail⟩
      have hp : noDtDtc s c = true ∧ noDtDt s d = true := by
        simpa [noDtDt, native_and, Bool.and_eq_true] using hHead
      have hRec := ih hTail
      exact ⟨⟨hp.1, hRec.1⟩, ⟨hp.2, hRec.2⟩⟩

private theorem ChainNoDtDt_descend
    (W : SmtDatatype) :
    ∀ (REST : SubstChain) (q : native_String) (Y : SmtDatatype),
      ChainNoDtDt REST W →
      ChainNoDtDt (chain_descend REST q Y) W
  | [], q, Y, _ => trivial
  | (s, R, P) :: REST, q, Y, h => by
      rcases h with ⟨hHead, hTail⟩
      cases hsq : native_streq s q with
      | true =>
          simpa [chain_descend, hsq] using
            ChainNoDtDt_descend W REST q Y hTail
      | false =>
          simp only [chain_descend, hsq, if_false]
          exact ⟨hHead,
            ChainNoDtDt_descend W REST q
              (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y) hTail⟩

private theorem ChainNoDtDt_append
    (REST : SubstChain) (q : native_String) (X P W : SmtDatatype)
    (hREST : ChainNoDtDt REST W) (hNew : noDtDt q W = true) :
    ChainNoDtDt (REST ++ [(q, X, P)]) W := by
  induction REST with
  | nil => exact ⟨hNew, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s, R, Q⟩
      rcases hREST with ⟨hHead, hTail⟩
      exact ⟨hHead, ih hTail⟩

private theorem namesConsTy_parts
    (root : SmtDatatype) (q : native_String) (X : SmtDatatype)
    (h : __smtx_type_names_consistent_rec root
      (SmtType.Datatype q X) = true) :
    __smtx_dt_name_agrees q X root = true ∧
      __smtx_dt_names_consistent_rec root X = true := by
  simp only [__smtx_type_names_consistent_rec] at h
  cases ha : __smtx_dt_name_agrees q X root <;>
    cases hc : __smtx_dt_names_consistent_rec root X <;>
      simp_all [native_ite]

private theorem namesConsDtc_parts
    (root : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons)
    (h : __smtx_dt_cons_names_consistent_rec root
      (SmtDatatypeCons.cons T c) = true) :
    __smtx_type_names_consistent_rec root T = true ∧
      __smtx_dt_cons_names_consistent_rec root c = true := by
  simp only [__smtx_dt_cons_names_consistent_rec] at h
  cases ht : __smtx_type_names_consistent_rec root T <;>
    cases hc : __smtx_dt_cons_names_consistent_rec root c <;>
      simp_all [native_ite]

private theorem namesConsDt_parts
    (root : SmtDatatype) (c : SmtDatatypeCons) (d : SmtDatatype)
    (h : __smtx_dt_names_consistent_rec root (SmtDatatype.sum c d) = true) :
    __smtx_dt_cons_names_consistent_rec root c = true ∧
      __smtx_dt_names_consistent_rec root d = true := by
  simp only [__smtx_dt_names_consistent_rec] at h
  cases hc : __smtx_dt_cons_names_consistent_rec root c <;>
    cases hd : __smtx_dt_names_consistent_rec root d <;>
      simp_all [native_ite]

mutual
private theorem noStrayTy_of_name_agrees
    (s : native_String) (X : SmtDatatype) :
    ∀ T : SmtType,
      __smtx_type_name_agrees s X T = true → noStrayTy s X T = true
  | SmtType.Datatype q D, h => by
      by_cases hEq : native_Teq
          (SmtType.Datatype s X) (SmtType.Datatype q D) = true
      · simp [noStrayTy, native_ite, hEq]
      · have hsq : native_streq q s = false := by
          cases hqs : native_streq q s with
          | false => rfl
          | true =>
              have hsq' : native_streq s q = true := by
                simpa [native_streq, eq_comm] using hqs
              simp [__smtx_type_name_agrees, native_ite, hsq', hEq] at h
        have hBody : __smtx_dt_name_agrees s X D = true := by
          have hsq' : native_streq s q = false := by
            simpa [native_streq, eq_comm] using hsq
          simpa [__smtx_type_name_agrees, native_ite, hsq'] using h
        simp [noStrayTy, native_ite, hEq, native_and, native_not, hsq,
          noStrayDt_of_name_agrees s X D hBody]
  | SmtType.None, _ => by simp [noStrayTy]
  | SmtType.Bool, _ => by simp [noStrayTy]
  | SmtType.Int, _ => by simp [noStrayTy]
  | SmtType.Real, _ => by simp [noStrayTy]
  | SmtType.RegLan, _ => by simp [noStrayTy]
  | SmtType.BitVec w, _ => by simp [noStrayTy]
  | SmtType.Map A B, _ => by simp [noStrayTy]
  | SmtType.Set A, _ => by simp [noStrayTy]
  | SmtType.Seq A, _ => by simp [noStrayTy]
  | SmtType.Char, _ => by simp [noStrayTy]
  | SmtType.TypeRef r, _ => by simp [noStrayTy]
  | SmtType.USort u, _ => by simp [noStrayTy]
  | SmtType.FunType A B, _ => by simp [noStrayTy]
  | SmtType.DtcAppType A B, _ => by simp [noStrayTy]

private theorem noStrayDtc_of_name_agrees
    (s : native_String) (X : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      __smtx_dt_cons_name_agrees s X c = true → noStrayDtc s X c = true
  | SmtDatatypeCons.unit, _ => by simp [noStrayDtc]
  | SmtDatatypeCons.cons T c, h => by
      have hp : __smtx_type_name_agrees s X T = true ∧
          __smtx_dt_cons_name_agrees s X c = true := by
        simp only [__smtx_dt_cons_name_agrees] at h
        cases ht : __smtx_type_name_agrees s X T <;>
          cases hc : __smtx_dt_cons_name_agrees s X c <;>
            simp_all [native_ite]
      simp [noStrayDtc, native_and,
        noStrayTy_of_name_agrees s X T hp.1,
        noStrayDtc_of_name_agrees s X c hp.2]

private theorem noStrayDt_of_name_agrees
    (s : native_String) (X : SmtDatatype) :
    ∀ d : SmtDatatype,
      __smtx_dt_name_agrees s X d = true → noStrayDt s X d = true
  | SmtDatatype.null, _ => by simp [noStrayDt]
  | SmtDatatype.sum c d, h => by
      have hp : __smtx_dt_cons_name_agrees s X c = true ∧
          __smtx_dt_name_agrees s X d = true := by
        simp only [__smtx_dt_name_agrees] at h
        cases hc : __smtx_dt_cons_name_agrees s X c <;>
          cases hd : __smtx_dt_name_agrees s X d <;>
            simp_all [native_ite]
      simp [noStrayDt, native_and,
        noStrayDtc_of_name_agrees s X c hp.1,
        noStrayDt_of_name_agrees s X d hp.2]
end

private theorem noStray_liftSources
    (s : native_String) (X : SmtDatatype) :
    ∀ (REST : SubstChain) (R : SmtDatatype),
      ChainNoDtDt REST X → noStrayDt s X R = true →
      noStrayDt s X (liftSources REST R) = true
  | [], R, _hNoDt, h => h
  | (q, Q, P) :: REST, R, hNoDt, h => by
      rcases hNoDt with ⟨hX, hTail⟩
      have hXFix : __smtx_dt_lift q Q X = X :=
        lift_noop_no_dt_dt q Q X hX
      exact noStray_liftSources s X REST (__smtx_dt_lift q Q R) hTail
        (noStray_lift_dt q Q s X hXFix R h)

mutual
def LocalNoSelfTy : SmtType → Bool
  | SmtType.Datatype s X => native_and (noDtDt s X) (LocalNoSelfDt X)
  | _ => true
def LocalNoSelfDtc : SmtDatatypeCons → Bool
  | SmtDatatypeCons.unit => true
  | SmtDatatypeCons.cons T c =>
      native_and (LocalNoSelfTy T) (LocalNoSelfDtc c)
def LocalNoSelfDt : SmtDatatype → Bool
  | SmtDatatype.null => true
  | SmtDatatype.sum c d =>
      native_and (LocalNoSelfDtc c) (LocalNoSelfDt d)
end

private def RootEmbeddedTy (root : SmtDatatype) (T : SmtType) : Prop :=
  ∀ s X, __smtx_dt_name_agrees s X root = true →
    __smtx_type_name_agrees s X T = true

private def RootEmbeddedDtc (root : SmtDatatype)
    (c : SmtDatatypeCons) : Prop :=
  ∀ s X, __smtx_dt_name_agrees s X root = true →
    __smtx_dt_cons_name_agrees s X c = true

private def RootEmbeddedDt (root : SmtDatatype) (d : SmtDatatype) : Prop :=
  ∀ s X, __smtx_dt_name_agrees s X root = true →
    __smtx_dt_name_agrees s X d = true

private theorem RootEmbeddedDt_parts
    (root : SmtDatatype) (c : SmtDatatypeCons) (d : SmtDatatype)
    (h : RootEmbeddedDt root (SmtDatatype.sum c d)) :
    RootEmbeddedDtc root c ∧ RootEmbeddedDt root d := by
  constructor <;> intro s X hRoot
  · have hAll := h s X hRoot
    simp only [__smtx_dt_name_agrees] at hAll
    cases hc : __smtx_dt_cons_name_agrees s X c <;>
      cases hd : __smtx_dt_name_agrees s X d <;>
        simp_all [native_ite]
  · have hAll := h s X hRoot
    simp only [__smtx_dt_name_agrees] at hAll
    cases hc : __smtx_dt_cons_name_agrees s X c <;>
      cases hd : __smtx_dt_name_agrees s X d <;>
        simp_all [native_ite]

private theorem RootEmbeddedDtc_parts
    (root : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons)
    (h : RootEmbeddedDtc root (SmtDatatypeCons.cons T c)) :
    RootEmbeddedTy root T ∧ RootEmbeddedDtc root c := by
  constructor <;> intro s X hRoot
  · have hAll := h s X hRoot
    simp only [__smtx_dt_cons_name_agrees] at hAll
    cases ht : __smtx_type_name_agrees s X T <;>
      cases hc : __smtx_dt_cons_name_agrees s X c <;>
        simp_all [native_ite]
  · have hAll := h s X hRoot
    simp only [__smtx_dt_cons_name_agrees] at hAll
    cases ht : __smtx_type_name_agrees s X T <;>
      cases hc : __smtx_dt_cons_name_agrees s X c <;>
        simp_all [native_ite]

private theorem RootEmbeddedTy_body
    (root : SmtDatatype) (q : native_String) (X : SmtDatatype)
    (h : RootEmbeddedTy root (SmtType.Datatype q X)) :
    RootEmbeddedDt root X := by
  intro s D hRoot
  have hAll := h s D hRoot
  simp only [__smtx_type_name_agrees] at hAll
  cases hsq : native_streq s q <;>
    cases hEq : native_Teq (SmtType.Datatype s D) (SmtType.Datatype q X) <;>
      cases hb : __smtx_dt_name_agrees s D X <;>
        simp_all [native_ite]

mutual
private theorem localNoSelf_ty
    (root : SmtDatatype) :
    ∀ T : SmtType,
      __smtx_type_names_consistent_rec root T = true →
      RootEmbeddedTy root T → LocalNoSelfTy T = true
  | SmtType.Datatype q X, hCons, hEmb => by
      have hp := namesConsTy_parts root q X hCons
      have hAt := hEmb q X hp.1
      have hSelf : __smtx_dt_name_agrees q X X = true := by
        simpa [__smtx_type_name_agrees, native_ite, native_streq, native_Teq]
          using hAt
      have hNo : noDtDt q X = true :=
        noDtDt_of_name_agrees_le q X X (Nat.le_refl _) hSelf
      simp [LocalNoSelfTy, native_and, hNo,
        localNoSelf_dt root X hp.2 (RootEmbeddedTy_body root q X hEmb)]
  | SmtType.None, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Bool, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Int, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Real, _, _ => by simp [LocalNoSelfTy]
  | SmtType.RegLan, _, _ => by simp [LocalNoSelfTy]
  | SmtType.BitVec w, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Map A B, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Set A, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Seq A, _, _ => by simp [LocalNoSelfTy]
  | SmtType.Char, _, _ => by simp [LocalNoSelfTy]
  | SmtType.TypeRef r, _, _ => by simp [LocalNoSelfTy]
  | SmtType.USort u, _, _ => by simp [LocalNoSelfTy]
  | SmtType.FunType A B, _, _ => by simp [LocalNoSelfTy]
  | SmtType.DtcAppType A B, _, _ => by simp [LocalNoSelfTy]

private theorem localNoSelf_dtc
    (root : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      __smtx_dt_cons_names_consistent_rec root c = true →
      RootEmbeddedDtc root c → LocalNoSelfDtc c = true
  | SmtDatatypeCons.unit, _, _ => by simp [LocalNoSelfDtc]
  | SmtDatatypeCons.cons T c, hCons, hEmb => by
      have hc := namesConsDtc_parts root T c hCons
      have he := RootEmbeddedDtc_parts root T c hEmb
      simp [LocalNoSelfDtc, native_and,
        localNoSelf_ty root T hc.1 he.1,
        localNoSelf_dtc root c hc.2 he.2]

private theorem localNoSelf_dt
    (root : SmtDatatype) :
    ∀ d : SmtDatatype,
      __smtx_dt_names_consistent_rec root d = true →
      RootEmbeddedDt root d → LocalNoSelfDt d = true
  | SmtDatatype.null, _, _ => by simp [LocalNoSelfDt]
  | SmtDatatype.sum c d, hCons, hEmb => by
      have hd := namesConsDt_parts root c d hCons
      have he := RootEmbeddedDt_parts root c d hEmb
      simp [LocalNoSelfDt, native_and,
        localNoSelf_dtc root c hd.1 he.1,
        localNoSelf_dt root d hd.2 he.2]
end

theorem localNoSelf_of_names_consistent
    (s : native_String) (d : SmtDatatype)
    (h : __smtx_type_names_consistent (SmtType.Datatype s d) = true) :
    LocalNoSelfDt d = true := by
  have hRec : __smtx_dt_names_consistent_rec d d = true := by
    simp only [__smtx_type_names_consistent] at h
    cases ha : __smtx_dt_name_agrees s d d <;>
      cases hc : __smtx_dt_names_consistent_rec d d <;>
        simp_all [native_ite]
  exact localNoSelf_dt d d hRec (fun _ _ hRoot => hRoot)

/-- The pump invariant of a chain: its head entry `(t, R, P)` resolves through
the whole chain to an inhabited datatype whose diagonal fold is well-formed
against the current payload `P` and positionally related to it.  `R` records
the name-consistent raw body from which `P` was obtained. -/
private def ChainOK : SubstChain → Prop
  | [] => True
  | (t, R, P) :: REST =>
      ∃ D : SmtDatatype,
        chain_ty ((t, R, P) :: REST) (SmtType.TypeRef t) = SmtType.Datatype t D ∧
        native_inhabited_type (SmtType.Datatype t D) = true ∧
        __smtx_dt_wf_rec (__smtx_dt_substitute t D D) P = true ∧
        FSkelDt (__smtx_dt_substitute t D D) P ∧
        ChainSourceOK t R P REST

/-- Packaging: the head entry facts for the *canonical* resolved body imply
the chain invariant; the resolution-shape and positional-skeleton components
hold generically. -/
private theorem chainok_head_facts
    (t : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (hFacts :
      native_inhabited_type
        (SmtType.Datatype t (chain_dt (chain_descend REST t P) P)) = true ∧
      __smtx_dt_wf_rec
        (__smtx_dt_substitute t (chain_dt (chain_descend REST t P) P)
          (chain_dt (chain_descend REST t P) P)) P = true) :
    ChainSourceOK t R P REST →
    ChainOK ((t, R, P) :: REST) := by
  intro hSource
  refine ⟨chain_dt (chain_descend REST t P) P, ?_, hFacts.1, hFacts.2, ?_,
    hSource⟩
  · rw [show chain_ty ((t, R, P) :: REST) (SmtType.TypeRef t) =
        chain_ty REST (__smtx_type_substitute t P (SmtType.TypeRef t)) from rfl]
    rw [show __smtx_type_substitute t P (SmtType.TypeRef t) =
        SmtType.Datatype t P by
      simp [__smtx_type_substitute, native_ite, native_streq]]
    exact chain_ty_datatype REST t P
  · have h := fskel_master_dt P
      (chain_descend REST t P ++
        [(t, R, chain_dt (chain_descend REST t P) P)])
    rwa [chain_dt_append_one] at h

/-- A root-consistent nested field can be folded out of and substituted back
into a diagonally well-formed parent without changing the parent payload. -/
private theorem parent_child_roundtrip
    (sP : native_String) (dP : SmtDatatype)
    (hPWf : __smtx_type_wf_rec (SmtType.Datatype sP dP)
      (SmtType.Datatype sP dP) = true)
    (hPNC : __smtx_type_names_consistent (SmtType.Datatype sP dP) = true)
    (sC : native_String) (dC : SmtDatatype)
    (hne : native_streq sP sC = false)
    (hFieldNC : __smtx_type_names_consistent_rec dP
      (SmtType.Datatype sC dC) = true) :
    __smtx_dt_substitute sC dC (__smtx_dt_lift sC dC dP) = dP := by
  have hRootCons : __smtx_dt_names_consistent_rec dP dP = true := by
    simp only [__smtx_type_names_consistent] at hPNC
    cases ha : __smtx_dt_name_agrees sP dP dP <;>
      cases hc : __smtx_dt_names_consistent_rec dP dP <;>
        simp_all [native_ite]
  have hFree :
      hasFreeDt sC (native_reflist_insert native_reflist_nil sP) dP = false := by
    have h := hasFreeTy_eq_false_of_wf sC (SmtType.Datatype sP dP) hPWf
    simpa [hasFreeTy] using h
  have hNot :
      native_reflist_contains
        (native_reflist_insert native_reflist_nil sP) sC = false := by
    have hsne : sC ≠ sP := by
      intro hEq
      subst sC
      simp [native_streq] at hne
    simp [native_reflist_contains, native_reflist_insert, native_reflist_nil,
      hsne]
  exact subst_lift_roundtrip_dt_of_names dP sC dC
    (native_reflist_insert native_reflist_nil sP)
    hRootCons hFieldNC hFree hNot

/-- The non-stable descent case, restricted to a subtree that actually uses
the head binder.

`hUse` rules out the original unrelated-subtree counterexample, but it is not
by itself sufficient.  There is also a demanded counterexample with
`X = [TypeRef a]`, a child named `b`, and a parent containing two nested
`Datatype b` occurrences with different bodies: all hypotheses below hold,
while the rotated parent fails `wfDt`.  In concrete constructor notation one
can take

* `P = [[Datatype b [[Datatype b [TypeRef b]]]]; []; []]`, and
* `X = [TypeRef a]`.

The failure is exactly the mismatched-body alias for `b`; the rotated parent
remains inhabited.  Production callers exclude this shape with
`__smtx_type_names_consistent`, so the proof below must additionally carry
the corresponding `consistentWith*` occurrence invariant through the
establishment walk.

Even with consistent names the residual case is genuine cycle rotation, not
list bookkeeping: it is already present with `REST = []` when `X` refers back
to `t`.  The resolved head can change, so the eventual proof must transport
its inhabited/wf facts rather than prove resolution equality.

Two pieces of that transport are now discharged above:

* `parent_child_roundtrip` proves the source-level lift/substitute inverse
  from root-relative name consistency and diagonal wf; and
* `inhabited_edge_rotate` proves the defaultability part of a single edge
  rotation once the resolved parent has no mismatched `s3` body.

The chain now retains `(name, raw body, payload)` rather than losing the raw
body.  `ChainSourceOK` proves that the evolving head payload is exactly the
base payload lifted through those recorded raw binders; `RawSuffixCons`
records that every binder is consistent with the fixed raw root; and the
establishment walk carries `ChainNoDt*`, which proves that a descent never
drops an earlier binder.  In particular, the proof below now derives
`noStrayDt s3 X P` for the *evolving payload* `P` before reaching the remaining
hole.

The resolved parent can still contain several rotated `s3` bodies, so
`noStrayDt s3 X D` is intentionally not claimed and the one-edge lemma cannot
be applied directly.  The residual obligation is now precisely the
simultaneous transport of the resolved head's inhabitedness and diagonal
`wf` from `hInh`/`hWf` and the newly closed node facts
`hInhNode`/`hWfNode`.  A name-set-only invariant remains insufficient because
payloads with the same resolved names can have different defaultability.

Caller-side finding: the folded child can itself be name-inconsistent even
when its raw source is consistent.  Consequently the diagonal oracle cannot
just add a consistency premise for its existing single body; it must retain
the raw guide separately from the folded payload, matching the distinction
made by the chain triples here.

Also, `chain_descend` does not commute syntactically with `selfExt`, even for
a globally consistent raw root: folding a child first can rotate the body of
an enclosing same-definition occurrence, after which a descent using its raw
body no longer recognizes that occurrence.  Therefore an induction that
rewrites the two operations into equality is not sound.  The next lemma must
be a confluence/transport statement over two valid raw histories, with the
strictly smaller recorded raw body supplying the induction measure; it cannot
be another substitution-normalization lemma. -/

/-
There is one further, essential restriction on "valid raw histories".  The
statement below is false with `ChainSourceOK` as currently defined because it
only reconstructs the head payload; `RawSuffixCons` deliberately ignores every
suffix payload.  Here is an exact counterexample (constructor lists are written
as lists of field lists):

* `t = a`, `s3 = b`, and the one suffix name is `u`;
* `X = [[TypeRef a], []]`;
* `U = [[Datatype b X]]` and `R = [[Datatype u U]]`;
* `P = lift u U R = [[TypeRef u]]`;
* `Y = substitute a (lift b X P) X`;
* `Q = [[Datatype b [[Datatype b Y]]]]`; and
* `rho = [(a, R, P), (u, U, Q)]`.

Lean evaluation confirms every premise of `chainok_selfExt_facts`, including
the old head's inhabitedness/diagonal wf and the newly closed `b` node's
inhabitedness/diagonal wf.  Nevertheless the head resolved after `selfExt rho
b X` is `[[Datatype u [[Datatype b [[TypeRef b]]]]]]`, which is uninhabited.

The bad `Q` cannot be produced by replaying `selfExt`: it hides a mismatched
`b` definition behind the `u` guide, where the old wf check skips it, and the
next rotation exposes it.  Requiring suffix payloads merely to be inhabited or
diagonally well-formed is insufficient (`Q` is both inhabited and diagonally
well-formed against itself).  The chain representation must carry construction
provenance for each payload (or an equivalent origin-indexed relation) before
this lemma can be proved.  In particular, adding another predicate only over
the raw suffix cannot repair the statement.
-/
private theorem chainok_selfExt_facts
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (hρ : ρ = (t, R, P) :: REST)
    (hne : native_streq t s3 = false)
    (hFresh : chainHasName s3 REST = false)
    (hField : __smtx_type_names_consistent_rec R
      (SmtType.Datatype s3 X) = true)
    (hNoNames : ChainNoDtDt REST X)
    (hOK : ChainOK ρ)
    (hInhNode :
      native_inhabited_type
        (SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)) = true)
    (hWfNode :
      __smtx_dt_wf_rec
        (__smtx_dt_substitute s3 (chain_dt (chain_descend ρ s3 X) X)
          (chain_dt (chain_descend ρ s3 X) X)) X = true)
    (hUse : usesHeadDt t X = true)
    (hUnstable :
      chain_ty (selfExt ρ s3 X) (SmtType.TypeRef t) ≠
        chain_ty ρ (SmtType.TypeRef t)) :
    ChainOK (selfExt ρ s3 X) := by
  subst hρ
  rcases hOK with ⟨D, hRes, hInh, hWf, hSkel, hSource⟩
  have hFieldParts := namesConsTy_parts R s3 X hField
  have hNoStrayR : noStrayDt s3 X R = true :=
    noStrayDt_of_name_agrees s3 X R hFieldParts.1
  have hNoStrayP : noStrayDt s3 X P = true := by
    rw [hSource.1]
    exact noStray_liftSources s3 X REST R hNoNames hNoStrayR
  have hSelfExt :
      selfExt ((t, R, P) :: REST) s3 X =
        (t, R, __smtx_dt_lift s3 X P) ::
          (chain_descend REST s3
            (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
            [(s3, X,
              chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]) := by
    simp [selfExt, chain_descend, hne]
  rw [hSelfExt]
  refine chainok_head_facts t R (__smtx_dt_lift s3 X P)
    (chain_descend REST s3
      (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
      [(s3, X,
        chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]) ?_
    (ChainSourceOK_descend t s3 R P X
      (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X)
      (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)
      REST hSource hFresh hField)
  sorry

/-- The chain invariant is preserved by a descent step when the descended
body uses the head binder.  In the stable case the facts transport along the
guide lift; the non-stable case is handled only under the demand condition
that makes those facts observable in the recursive walk. -/
private theorem chainok_selfExt_needed
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (hρ : ρ = (t, R, P) :: REST)
    (hne : native_streq t s3 = false)
    (hFresh : chainHasName s3 REST = false)
    (hField : __smtx_type_names_consistent_rec R
      (SmtType.Datatype s3 X) = true)
    (hNoNames : ChainNoDtDt REST X)
    (hOK : ChainOK ρ)
    (hInhNode :
      native_inhabited_type
        (SmtType.Datatype s3 (chain_dt (chain_descend ρ s3 X) X)) = true)
    (hWfNode :
      __smtx_dt_wf_rec
        (__smtx_dt_substitute s3 (chain_dt (chain_descend ρ s3 X) X)
          (chain_dt (chain_descend ρ s3 X) X)) X = true)
    (hUse : usesHeadDt t X = true) :
    ChainOK (selfExt ρ s3 X) := by
  by_cases hStable :
      chain_ty (selfExt ρ s3 X) (SmtType.TypeRef t) =
        chain_ty ρ (SmtType.TypeRef t)
  · -- stable resolution: transport the facts along the head-payload lift
    subst hρ
    rcases hOK with ⟨D, hRes, hInh, hWf, hSkel, hSource⟩
    -- the descended chain has head `(t, lift s3 X P)`
    have hSelfExt :
        selfExt ((t, R, P) :: REST) s3 X =
          (t, R, __smtx_dt_lift s3 X P) ::
            (chain_descend REST s3
              (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
              [(s3, X,
                chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]) := by
      simp [selfExt, chain_descend, hne]
    rw [hSelfExt]
    refine ⟨D, ?_, hInh, ?_, ?_, ?_⟩
    · rw [← hSelfExt, hStable]
      exact hRes
    · exact guideTrDt_wf (lift_guide_tr_dt s3 X hSkel) hWf
    · exact fskel_lift_dt s3 X hSkel
    · exact ChainSourceOK_descend t s3 R P X
        (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X)
        (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)
        REST hSource hFresh hField
  · exact chainok_selfExt_facts ρ s3 X t R P REST hρ hne hFresh hField
      hNoNames hOK hInhNode hWfNode hUse hStable

/-! The establishment walk: over a raw guide `dU`, the image under a chain
with head `(t, P)` transports the guide from `dU` to `dt_substitute t P dU`,
given the chain invariant and the old well-formedness (whose pattern-2 facts
feed the chain-invariant maintenance at nested descents). -/
mutual

private theorem estab_ty :
    ∀ (TU : SmtType) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_type_names_consistent_rec R TU = true →
      LocalNoSelfTy TU = true →
      ChainNoDtTy REST TU →
      (usesHeadTy t TU = true → ChainOK ((t, R, P) :: REST)) →
      (∀ (s3 : native_String) (X : SmtDatatype), TU = SmtType.Datatype s3 X →
        native_inhabited_type (chain_ty ((t, R, P) :: REST) TU) = true ∧
          __smtx_type_wf_rec (chain_ty ((t, R, P) :: REST) TU) TU = true) →
      GuideTr (chain_ty ((t, R, P) :: REST) TU) TU
        (__smtx_type_substitute t P TU)
  | SmtType.TypeRef r, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      hNeed, _hOldField => by
      cases hs : native_streq t r with
      | true =>
          have hEq : t = r := by simpa [native_streq] using hs
          subst r
          have hOK : ChainOK ((t, R, P) :: REST) :=
            hNeed (by simp [usesHeadTy, native_streq])
          rcases hOK with ⟨D, hRes, hInh, hWf, _hSkel, _hSource⟩
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
  | SmtType.Datatype s3 X, t, R, P, REST, hCons, hLocal, hNoDt,
      hNeed, hOldField => by
      have hConsParts := namesConsTy_parts R s3 X hCons
      have hLocalParts : noDtDt s3 X = true ∧ LocalNoSelfDt X = true := by
        simpa [LocalNoSelfTy, native_and, Bool.and_eq_true] using hLocal
      have hNoDtParts := ChainNoDtTy_datatype_parts REST s3 X hNoDt
      cases hs : native_streq t s3 with
      | true =>
          rw [show __smtx_type_substitute t P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3 X by
            simp [__smtx_type_substitute, native_ite, hs]]
          exact GuideTr.same _ _
      | false =>
          have hFacts := hOldField s3 X rfl
          rw [chain_ty_datatype ((t, R, P) :: REST) s3 X] at hFacts
          have hInhNode :
              native_inhabited_type
                (SmtType.Datatype s3
                  (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)) = true :=
            hFacts.1
          have hWfNode :
              __smtx_dt_wf_rec
                (__smtx_dt_substitute s3
                  (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)
                  (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)) X = true := by
            simpa [__smtx_type_wf_rec] using hFacts.2
          rw [chain_ty_datatype ((t, R, P) :: REST) s3 X]
          rw [show __smtx_type_substitute t P (SmtType.Datatype s3 X) =
              SmtType.Datatype s3
                (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) by
            simp [__smtx_type_substitute, native_ite, hs]]
          refine GuideTr.dtRec ?_
          -- the descended chain has head `(t, lift s3 X P)`
          have hDesc :
              chain_descend ((t, R, P) :: REST) s3 X =
                (t, R, __smtx_dt_lift s3 X P) ::
                  chain_descend REST s3
                    (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) := by
            simp [chain_descend, hs]
          have hNeed' : usesHeadDt t X = true →
              ChainOK (selfExt ((t, R, P) :: REST) s3 X) := by
            intro hUse
            have hOK : ChainOK ((t, R, P) :: REST) := hNeed (by
              simp [usesHeadTy, hs, hUse])
            exact chainok_selfExt_needed ((t, R, P) :: REST) s3 X t R P REST
              rfl hs hNoDtParts.1 hCons hNoDtParts.2 hOK hInhNode hWfNode hUse
          have hSelfExtEq : selfExt ((t, R, P) :: REST) s3 X =
              (t, R, __smtx_dt_lift s3 X P) ::
                (chain_descend REST s3
                  (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                  [(s3, X,
                    chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]) := by
            simp [selfExt, hDesc]
          -- the folded side of the child chain is the node's diagonal fold
          have hFold :
              chain_dt
                ((t, R, __smtx_dt_lift s3 X P) ::
                  (chain_descend REST s3
                    (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                    [(s3, X,
                      chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)])) X =
                __smtx_dt_substitute s3
                  (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)
                  (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X) := by
            rw [show ((t, R, __smtx_dt_lift s3 X P) ::
                (chain_descend REST s3
                  (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
                  [(s3, X,
                    chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)])) =
              (chain_descend ((t, R, P) :: REST) s3 X ++
                [(s3, X,
                  chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]) by
              simp [hDesc]]
            rw [chain_dt_append_one]
          have hWalk := estab_dt X t R (__smtx_dt_lift s3 X P)
            (chain_descend REST s3
              (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X) ++
              [(s3, X,
                chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)])
            hConsParts.2 hLocalParts.2
            (ChainNoDtDt_append
              (chain_descend REST s3
                (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X))
              s3 X (chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X) X
              (ChainNoDtDt_descend X REST s3
                (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X)
                hNoDtParts.2)
              hLocalParts.1)
            (by
              intro hUse
              have hOK' := hNeed' hUse
              rwa [hSelfExtEq] at hOK')
            (by rw [hFold]; exact hWfNode)
          rwa [hFold] at hWalk
  | SmtType.None, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.None = SmtType.None by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Bool, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Bool = SmtType.Bool by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Int, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Int = SmtType.Int by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Real, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Real = SmtType.Real by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.RegLan, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.RegLan = SmtType.RegLan by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.BitVec w, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.BitVec w) = SmtType.BitVec w by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Map A B, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Map A B) = SmtType.Map A B by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Set A, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Set A) = SmtType.Set A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Seq A, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Seq A) = SmtType.Seq A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Char, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Char = SmtType.Char by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.USort u, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.USort u) = SmtType.USort u by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.FunType A B, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.DtcAppType A B, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _

private theorem estab_dtc :
    ∀ (cU : SmtDatatypeCons) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_dt_cons_names_consistent_rec R cU = true →
      LocalNoSelfDtc cU = true →
      ChainNoDtDtc REST cU →
      (usesHeadDtc t cU = true → ChainOK ((t, R, P) :: REST)) →
      __smtx_dt_cons_wf_rec (chain_dtc ((t, R, P) :: REST) cU) cU = true →
      GuideTrDtc (chain_dtc ((t, R, P) :: REST) cU) cU
        (__smtx_dtc_substitute t P cU)
  | SmtDatatypeCons.unit, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOld => by
      rw [chain_dtc_unit]
      rw [show __smtx_dtc_substitute t P SmtDatatypeCons.unit =
        SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact GuideTrDtc.unit
  | SmtDatatypeCons.cons TU cU, t, R, P, REST, hCons, hLocal, hNoDt,
      hNeed, hOld => by
      have hConsParts := namesConsDtc_parts R TU cU hCons
      have hNoDtParts := ChainNoDtDtc_parts REST TU cU hNoDt
      have hLocalParts : LocalNoSelfTy TU = true ∧
          LocalNoSelfDtc cU = true := by
        simpa [LocalNoSelfDtc, native_and, Bool.and_eq_true] using hLocal
      rw [chain_dtc_cons] at hOld
      have hTail :
          __smtx_dt_cons_wf_rec (chain_dtc ((t, R, P) :: REST) cU) cU = true :=
        dt_cons_wf_tail hOld
      have hOldField : ∀ (s3 : native_String) (X : SmtDatatype),
          TU = SmtType.Datatype s3 X →
          native_inhabited_type (chain_ty ((t, R, P) :: REST) TU) = true ∧
            __smtx_type_wf_rec (chain_ty ((t, R, P) :: REST) TU) TU = true := by
        intro s3 X hTU
        subst hTU
        have hParts := dt_cons_wf_p2_parts
          (fun _ _ _ _ hEq => by cases hEq) hOld
        exact ⟨hParts.1, hParts.2.1⟩
      rw [chain_dtc_cons]
      rw [show __smtx_dtc_substitute t P (SmtDatatypeCons.cons TU cU) =
        SmtDatatypeCons.cons (__smtx_type_substitute t P TU)
          (__smtx_dtc_substitute t P cU) by simp [__smtx_dtc_substitute]]
      have hNeedHead : usesHeadTy t TU = true → ChainOK ((t, R, P) :: REST) := by
        intro hUse
        exact hNeed (by simp [usesHeadDtc, native_or, hUse])
      have hNeedTail : usesHeadDtc t cU = true → ChainOK ((t, R, P) :: REST) := by
        intro hUse
        exact hNeed (by simp [usesHeadDtc, native_or, hUse])
      exact GuideTrDtc.cons
        (estab_ty TU t R P REST hConsParts.1 hLocalParts.1 hNoDtParts.1
          hNeedHead hOldField)
        (estab_dtc cU t R P REST hConsParts.2 hLocalParts.2 hNoDtParts.2
          hNeedTail hTail)

private theorem estab_dt :
    ∀ (dU : SmtDatatype) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_dt_names_consistent_rec R dU = true →
      LocalNoSelfDt dU = true →
      ChainNoDtDt REST dU →
      (usesHeadDt t dU = true → ChainOK ((t, R, P) :: REST)) →
      __smtx_dt_wf_rec (chain_dt ((t, R, P) :: REST) dU) dU = true →
      GuideTrDt (chain_dt ((t, R, P) :: REST) dU) dU
        (__smtx_dt_substitute t P dU)
  | SmtDatatype.null, t, R, P, REST, _hCons, _hLocal, _hNoDt,
      _hOK, _hOld => by
      rw [chain_dt_null]
      rw [show __smtx_dt_substitute t P SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_substitute]]
      exact GuideTrDt.null
  | SmtDatatype.sum cU dU, t, R, P, REST, hCons, hLocal, hNoDt,
      hNeed, hOld => by
      have hConsParts := namesConsDt_parts R cU dU hCons
      have hNoDtParts := ChainNoDtDt_parts REST cU dU hNoDt
      have hLocalParts : LocalNoSelfDtc cU = true ∧
          LocalNoSelfDt dU = true := by
        simpa [LocalNoSelfDt, native_and, Bool.and_eq_true] using hLocal
      rw [chain_dt_sum] at hOld
      have hParts := dt_wf_sum_parts hOld
      rw [chain_dt_sum]
      rw [show __smtx_dt_substitute t P (SmtDatatype.sum cU dU) =
        SmtDatatype.sum (__smtx_dtc_substitute t P cU)
          (__smtx_dt_substitute t P dU) by simp [__smtx_dt_substitute]]
      have hNeedHead : usesHeadDtc t cU = true → ChainOK ((t, R, P) :: REST) := by
        intro hUse
        exact hNeed (by simp [usesHeadDt, native_or, hUse])
      have hNeedTail : usesHeadDt t dU = true → ChainOK ((t, R, P) :: REST) := by
        intro hUse
        exact hNeed (by simp [usesHeadDt, native_or, hUse])
      exact GuideTrDt.sum
        (estab_dtc cU t R P REST hConsParts.1 hLocalParts.1 hNoDtParts.1
          hNeedHead hParts.1)
        (estab_dt dU t R P REST hConsParts.2 hLocalParts.2 hNoDtParts.2
          hNeedTail hParts.2)

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
    (hPNC : __smtx_type_names_consistent (SmtType.Datatype sP dP) = true)
    (sC : native_String) (dC : SmtDatatype)
    (hne : native_streq sP sC = false)
    (hFieldNC : __smtx_type_names_consistent_rec dP
      (SmtType.Datatype sC dC) = true)
    (hCNoSelf : noDtDt sC dC = true)
    (hCLocal : LocalNoSelfDt dC = true)
    (BC : SmtDatatype)
    (hBC : BC = __smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC)
    (hInhBC : native_inhabited_type (SmtType.Datatype sC BC) = true)
    (hOld : __smtx_dt_wf_rec (__smtx_dt_substitute sC BC BC) dC = true) :
    GuideTrDt (__smtx_dt_substitute sC BC BC) dC BC := by
  -- the base chain `[(sP, dP, dP)]` satisfies the invariant
  have hOK0 : ChainOK [(sP, dP, dP)] := by
    refine ⟨dP, ?_, hPInh, ?_, ?_, ?_⟩
    · simp [chain_ty, __smtx_type_substitute, native_ite, native_streq]
    · simpa [__smtx_type_wf_rec] using hPWf
    · exact fskel_master_dt dP [(sP, dP, dP)]
    · exact ⟨rfl, hPNC, trivial⟩
  -- the top chain is one descent step from it
  have hDesc0 :
      chain_descend [(sP, dP, dP)] sC dC =
        [(sP, dP, __smtx_dt_lift sC dC dP)] := by
    simp [chain_descend, hne]
  have hTop :
      selfExt [(sP, dP, dP)] sC dC =
        [(sP, dP, __smtx_dt_lift sC dC dP), (sC, dC, BC)] := by
    simp [selfExt, hDesc0, chain_dt, hBC]
  have hNode0 :
      chain_dt (chain_descend [(sP, dP, dP)] sC dC) dC = BC := by
    simp [chain_descend, hne, chain_dt, hBC]
  have hNeedTop : usesHeadDt sP dC = true →
      ChainOK [(sP, dP, __smtx_dt_lift sC dC dP), (sC, dC, BC)] := by
    intro hUse
    rw [← hTop]
    exact chainok_selfExt_needed [(sP, dP, dP)] sC dC sP dP dP []
      rfl hne rfl hFieldNC trivial hOK0
      (by rw [hNode0]; exact hInhBC) (by rw [hNode0]; exact hOld) hUse
  have hFold0 :
      chain_dt [(sP, dP, __smtx_dt_lift sC dC dP), (sC, dC, BC)] dC =
        __smtx_dt_substitute sC BC BC := by
    simp [chain_dt, hBC]
  have hFieldParts := namesConsTy_parts dP sC dC hFieldNC
  have hWalk := estab_dt dC sP dP (__smtx_dt_lift sC dC dP)
    [(sC, dC, BC)] hFieldParts.2 hCLocal
    ⟨hCNoSelf, trivial⟩ hNeedTop
    (by rw [hFold0]; exact hOld)
  have hFold :
      chain_dt [(sP, dP, __smtx_dt_lift sC dC dP), (sC, dC, BC)] dC =
        __smtx_dt_substitute sC BC BC := by
    simp [chain_dt, hBC]
  rw [hFold, ← hBC] at hWalk
  exact hWalk

/-- Wf-diagonalization: the folded form of a nested datatype field of a
diagonal entry is itself diagonal.  `hFWf` is the field's well-formedness
against its raw guide, which the parent's own diagonal well-formedness
supplies at every nested datatype field.  The consistency premises are
deliberately source-level: folded bodies need not themselves remain name
consistent.  `hCNoSelf` and `hCLocal` are the destructured local consequences
of source name consistency used to keep the raw binder history fresh. -/
theorem wf_diag_push
    (sP : native_String) (dP : SmtDatatype)
    (hPInh : native_inhabited_type (SmtType.Datatype sP dP) = true)
    (hPWf : __smtx_type_wf_rec (SmtType.Datatype sP dP)
        (SmtType.Datatype sP dP) = true)
    (hPNC : __smtx_type_names_consistent (SmtType.Datatype sP dP) = true)
    (sC : native_String) (dC : SmtDatatype)
    (hFieldNC : __smtx_type_names_consistent_rec dP
      (SmtType.Datatype sC dC) = true)
    (hCNoSelf : noDtDt sC dC = true)
    (hCLocal : LocalNoSelfDt dC = true)
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
      have hTr := wf_diag_establish sP dP hPInh hPWf hPNC sC dC hs
        hFieldNC hCNoSelf hCLocal
        (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) rfl hFInh hOld
      simpa [__smtx_type_wf_rec] using guideTrDt_wf hTr hOld

end Smtm
