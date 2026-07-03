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

/-! ## Part 2: establishment for the diagonalization instance -/

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
    (hBC : BC = __smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) :
    GuideTrDt (__smtx_dt_substitute sC BC BC) dC BC := by
  sorry

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
      rw [hSub] at hFWf ⊢
      have hOld :
          __smtx_dt_wf_rec
            (__smtx_dt_substitute sC
              (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC)
              (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC))
            dC = true := by
        simpa [__smtx_type_wf_rec] using hFWf
      have hTr := wf_diag_establish sP dP hPInh hPWf sC dC hs
        (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) rfl
      simpa [__smtx_type_wf_rec] using guideTrDt_wf hTr hOld

end Smtm
