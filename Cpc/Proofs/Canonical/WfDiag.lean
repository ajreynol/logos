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

/-! ## Folded-side observational transport

`GuideTr` changes the raw/guide side while keeping the folded side fixed.
The non-stable history case needs the orthogonal operation: the guide is
fixed, while two canonical resolutions may differ below positions that the
guide presents as references.  `FoldObs* old new guide` records exactly what
the wf recursion can observe.

At a `TypeRef` guide, two datatype-shaped folded fields are indistinguishable
because `__smtx_dt_cons_wf_rec` takes its skip clause before inspecting either
body.  At an inline datatype guide, the new field must preserve
defaultability and the two diagonal bodies are compared recursively.  Equal
folded fields are always observationally related. -/

mutual

private inductive FoldObsTy : SmtType → SmtType → SmtType → Prop where
  | same (F U : SmtType) : FoldObsTy F F U
  /-- Away from datatype and reference guides, `type_wf_rec` depends only on
  the guide.  The folded field may therefore change arbitrarily. -/
  | masked {TOld TNew TU : SmtType}
      (hRef : ∀ r : native_String, TU ≠ SmtType.TypeRef r)
      (hDt : ∀ (q : native_String) (D : SmtDatatype),
        TU ≠ SmtType.Datatype q D)
      (hInh : native_inhabited_type TOld = true →
        native_inhabited_type TNew = true) :
      FoldObsTy TOld TNew TU
  | ref {sOld sNew r : native_String} {dOld dNew : SmtDatatype} :
      FoldObsTy (SmtType.Datatype sOld dOld)
        (SmtType.Datatype sNew dNew) (SmtType.TypeRef r)
  | deadRef {TOld TNew : SmtType} {r : native_String}
      (hOld : ∀ (s : native_String) (d : SmtDatatype),
        TOld ≠ SmtType.Datatype s d) :
      FoldObsTy TOld TNew (SmtType.TypeRef r)
  | dt {sOld sNew sU : native_String} {dOld dNew dU : SmtDatatype} :
      (native_inhabited_type (SmtType.Datatype sOld dOld) = true →
        native_inhabited_type (SmtType.Datatype sNew dNew) = true) →
      FoldObsDt (__smtx_dt_substitute sOld dOld dOld)
        (__smtx_dt_substitute sNew dNew dNew) dU →
      FoldObsTy (SmtType.Datatype sOld dOld)
        (SmtType.Datatype sNew dNew) (SmtType.Datatype sU dU)

private inductive FoldObsDtc :
    SmtDatatypeCons → SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : FoldObsDtc SmtDatatypeCons.unit SmtDatatypeCons.unit
      SmtDatatypeCons.unit
  | cons {TOld TNew TU : SmtType}
      {cOld cNew cU : SmtDatatypeCons} :
      FoldObsTy TOld TNew TU → FoldObsDtc cOld cNew cU →
      FoldObsDtc (SmtDatatypeCons.cons TOld cOld)
        (SmtDatatypeCons.cons TNew cNew) (SmtDatatypeCons.cons TU cU)

private inductive FoldObsDt : SmtDatatype → SmtDatatype → SmtDatatype → Prop where
  | null : FoldObsDt SmtDatatype.null SmtDatatype.null SmtDatatype.null
  | sum {cOld cNew cU : SmtDatatypeCons} {dOld dNew dU : SmtDatatype} :
      FoldObsDtc cOld cNew cU → FoldObsDt dOld dNew dU →
      FoldObsDt (SmtDatatype.sum cOld dOld) (SmtDatatype.sum cNew dNew)
        (SmtDatatype.sum cU dU)

end

mutual

private theorem foldObsTy_wf {TOld TNew TU : SmtType}
    (hObs : FoldObsTy TOld TNew TU)
    (hOld : __smtx_type_wf_rec TOld TU = true) :
    __smtx_type_wf_rec TNew TU = true :=
  match hObs with
  | FoldObsTy.same _ _ => hOld
  | @FoldObsTy.masked TOld TNew TU hRef hDt _hInh => by
      cases TU <;> first
        | exact absurd rfl (hRef _)
        | exact absurd rfl (hDt _ _)
        | simpa [__smtx_type_wf_rec] using hOld
  | @FoldObsTy.ref sOld sNew r dOld dNew => by
      simp [__smtx_type_wf_rec] at hOld
  | @FoldObsTy.deadRef TOld TNew r hNotDt => by
      simp [__smtx_type_wf_rec] at hOld
  | @FoldObsTy.dt sOld sNew sU dOld dNew dU _hInh hBody => by
      have hOldBody :
          __smtx_dt_wf_rec (__smtx_dt_substitute sOld dOld dOld) dU = true := by
        simpa [__smtx_type_wf_rec] using hOld
      simpa [__smtx_type_wf_rec] using foldObsDt_wf hBody hOldBody

private theorem foldObsDtc_wf {cOld cNew cU : SmtDatatypeCons}
    (hObs : FoldObsDtc cOld cNew cU)
    (hOld : __smtx_dt_cons_wf_rec cOld cU = true) :
    __smtx_dt_cons_wf_rec cNew cU = true :=
  match hObs with
  | FoldObsDtc.unit => hOld
  | @FoldObsDtc.cons TOld TNew TU cOld cNew cU hHead hTail => by
      have hTailOld : __smtx_dt_cons_wf_rec cOld cU = true :=
        dt_cons_wf_tail hOld
      have hTailNew := foldObsDtc_wf hTail hTailOld
      cases hHead with
      | same => exact dt_cons_wf_head_tail hOld hTailNew
      | @masked TOld TNew TU hRef hDt hInh =>
          have hParts := dt_cons_wf_p2_parts
            (fun _ _ r _ hTU => hRef r hTU) hOld
          exact dt_cons_wf_p2_intro (hInh hParts.1)
            (foldObsTy_wf (FoldObsTy.masked hRef hDt hInh) hParts.2.1)
            hTailNew
      | ref =>
          rw [dt_cons_wf_p1_iff]
          exact hTailNew
      | @deadRef TOld TNew r hNotDt =>
          have hParts := dt_cons_wf_p2_parts
            (fun s d _ hEq _ => hNotDt s d hEq) hOld
          exfalso
          simpa [__smtx_type_wf_rec] using hParts.2.1
      | @dt sOld sNew sU dOld dNew dU hInh hBody =>
          have hParts := dt_cons_wf_p2_parts
            (fun _ _ _ _ hEq => by cases hEq) hOld
          exact dt_cons_wf_p2_intro (hInh hParts.1)
            (foldObsTy_wf (FoldObsTy.dt hInh hBody) hParts.2.1) hTailNew

private theorem foldObsDt_wf {dOld dNew dU : SmtDatatype}
    (hObs : FoldObsDt dOld dNew dU)
    (hOld : __smtx_dt_wf_rec dOld dU = true) :
    __smtx_dt_wf_rec dNew dU = true :=
  match hObs with
  | FoldObsDt.null => hOld
  | @FoldObsDt.sum cOld cNew cU dOld dNew dU hHead hTail => by
      have hParts := dt_wf_sum_parts hOld
      simp [__smtx_dt_wf_rec, native_ite,
        foldObsDtc_wf hHead hParts.1, foldObsDt_wf hTail hParts.2]

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

private def chainRefsAcc : RefList → SubstChain → RefList
  | refs, [] => refs
  | refs, (s, _R, _P) :: ρ =>
      chainRefsAcc (native_reflist_insert refs s) ρ

private def chainRefs (ρ : SubstChain) : RefList :=
  chainRefsAcc native_reflist_nil ρ

/-- Applying a chain produces a positional substitution image of its source.
This deliberately says nothing about whether payloads came from the recorded
raw bodies; that stronger origin fact is maintained separately. -/
private theorem chain_dt_img_acc
    (refs : RefList) (X F : SmtDatatype) (hImg : imgDt refs F X) :
    ∀ ρ : SubstChain,
      imgDt (chainRefsAcc refs ρ) (chain_dt ρ F) X
  | [] => hImg
  | (s, R, P) :: ρ => by
      exact chain_dt_img_acc (native_reflist_insert refs s) X
        (__smtx_dt_substitute s P F)
        (imgDt_subst s P X F hImg) ρ

private theorem chain_dt_img (ρ : SubstChain) (X : SmtDatatype) :
    imgDt (chainRefs ρ) (chain_dt ρ X) X := by
  exact chain_dt_img_acc native_reflist_nil X X
    (imgDt_refl native_reflist_nil X) ρ

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

/-! A proof-relevant presentation of `refDef`.  The Boolean is convenient
for computation, while these witnesses expose the finite constructor path
that succeeds.  In particular, following a resolved reference gives a
strict subderivation (`DefPathTy.dt`), which is the induction measure for
transporting defaultability between two history resolutions. -/
mutual

private inductive DefPathTy (S : RefList) : SmtType → Prop where
  | ref {r : native_String} :
      native_reflist_contains S r = true → DefPathTy S (SmtType.TypeRef r)
  | dt {s : native_String} {D : SmtDatatype} :
      DefPathDt S D → DefPathTy S (SmtType.Datatype s D)
  | atom {T : SmtType}
      (hRef : ∀ r : native_String, T ≠ SmtType.TypeRef r)
      (hDt : ∀ (s : native_String) (D : SmtDatatype),
        T ≠ SmtType.Datatype s D)
      (hDef : refDefTy S T = true) : DefPathTy S T

private inductive DefPathDtc (S : RefList) : SmtDatatypeCons → Prop where
  | unit : DefPathDtc S SmtDatatypeCons.unit
  | cons {T : SmtType} {c : SmtDatatypeCons} :
      DefPathTy S T → DefPathDtc S c →
      DefPathDtc S (SmtDatatypeCons.cons T c)

private inductive DefPathDt (S : RefList) : SmtDatatype → Prop where
  | head {c : SmtDatatypeCons} {d : SmtDatatype} :
      DefPathDtc S c → DefPathDt S (SmtDatatype.sum c d)
  | tail {c : SmtDatatypeCons} {d : SmtDatatype} :
      DefPathDt S d → DefPathDt S (SmtDatatype.sum c d)

end

mutual

private theorem defPathTy_of_refDef (S : RefList) :
    ∀ T : SmtType, refDefTy S T = true → DefPathTy S T
  | SmtType.TypeRef r, h => DefPathTy.ref (by simpa [refDefTy] using h)
  | SmtType.Datatype s D, h =>
      DefPathTy.dt (defPathDt_of_refDef S D (by simpa [refDefTy] using h))
  | SmtType.None, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Bool, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Int, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Real, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.RegLan, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.BitVec w, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Map A B, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Set A, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Seq A, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.Char, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.USort u, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.FunType A B, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h
  | SmtType.DtcAppType A B, h => DefPathTy.atom
      (fun _ hEq => by cases hEq) (fun _ _ hEq => by cases hEq) h

private theorem defPathDtc_of_refDef (S : RefList) :
    ∀ c : SmtDatatypeCons, refDefDtc S c = true → DefPathDtc S c
  | SmtDatatypeCons.unit, _ => DefPathDtc.unit
  | SmtDatatypeCons.cons T c, h => by
      have hp : refDefTy S T = true ∧ refDefDtc S c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using h
      exact DefPathDtc.cons (defPathTy_of_refDef S T hp.1)
        (defPathDtc_of_refDef S c hp.2)

private theorem defPathDt_of_refDef (S : RefList) :
    ∀ D : SmtDatatype, refDefDt S D = true → DefPathDt S D
  | SmtDatatype.null, h => by simp [refDefDt] at h
  | SmtDatatype.sum c D, h => by
      have hp : refDefDtc S c = true ∨ refDefDt S D = true := by
        simpa [refDefDt, Bool.or_eq_true] using h
      rcases hp with hc | hD
      · exact DefPathDt.head (defPathDtc_of_refDef S c hc)
      · exact DefPathDt.tail (defPathDt_of_refDef S D hD)

end

mutual

private theorem refDef_of_defPathTy {S : RefList} {T : SmtType}
    (h : DefPathTy S T) : refDefTy S T = true :=
  match h with
  | DefPathTy.ref hr => by simpa [refDefTy] using hr
  | DefPathTy.dt hD => by simpa [refDefTy] using refDef_of_defPathDt hD
  | DefPathTy.atom _ _ hDef => hDef

private theorem refDef_of_defPathDtc {S : RefList} {c : SmtDatatypeCons}
    (h : DefPathDtc S c) : refDefDtc S c = true :=
  match h with
  | DefPathDtc.unit => by simp [refDefDtc]
  | DefPathDtc.cons hT hc => by
      simp [refDefDtc, Bool.and_eq_true,
        refDef_of_defPathTy hT, refDef_of_defPathDtc hc]

private theorem refDef_of_defPathDt {S : RefList} {D : SmtDatatype}
    (h : DefPathDt S D) : refDefDt S D = true :=
  match h with
  | DefPathDt.head hc => by
      simp [refDefDt, Bool.or_eq_true, refDef_of_defPathDtc hc]
  | DefPathDt.tail hD => by
      simp [refDefDt, Bool.or_eq_true, refDef_of_defPathDt hD]

end

/-! A reference-free default path is preserved by a positional substitution
image.  At a raw `TypeRef` the premise is impossible; everywhere else an
image has the same constructor shape, and datatype bodies recurse.  This is
the semantic payoff of recording origin images in the chain invariant: once
an evolved body is known to be an image of its raw source, inhabitance follows
without inspecting any of the payloads that produced the image. -/
mutual

private theorem refDef_img_ty (refs : RefList) :
    ∀ (U F : SmtType), imgTy refs F U →
      refDefTy native_reflist_nil U = true →
        refDefTy native_reflist_nil F = true
  | SmtType.TypeRef r, F, _hImg, hRef => by
      simp [refDefTy, native_reflist_contains, native_reflist_nil] at hRef
  | SmtType.Datatype s D, F, hImg, hRef => by
      rcases hImg with ⟨DF, rfl, hBody⟩
      have hD : refDefDt native_reflist_nil D = true := by
        simpa [refDefTy] using hRef
      simpa [refDefTy] using refDef_img_dt refs D DF hBody hD
  | SmtType.None, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Bool, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Int, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Real, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.RegLan, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.BitVec w, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Map A B, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Set A, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Seq A, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.Char, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.USort u, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.FunType A B, F, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtType.DtcAppType A B, F, hImg, hRef => by
      cases hImg
      exact hRef

private theorem refDef_img_dtc (refs : RefList) :
    ∀ (cU cF : SmtDatatypeCons), imgDtc refs cF cU →
      refDefDtc native_reflist_nil cU = true →
        refDefDtc native_reflist_nil cF = true
  | SmtDatatypeCons.unit, cF, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtDatatypeCons.cons T c, cF, hImg, hRef => by
      rcases hImg with ⟨TF, cF', rfl, hT, hc⟩
      have hp : refDefTy native_reflist_nil T = true ∧
          refDefDtc native_reflist_nil c = true := by
        simpa [refDefDtc, Bool.and_eq_true] using hRef
      simp [refDefDtc, Bool.and_eq_true,
        refDef_img_ty refs T TF hT hp.1,
        refDef_img_dtc refs c cF' hc hp.2]

private theorem refDef_img_dt (refs : RefList) :
    ∀ (dU dF : SmtDatatype), imgDt refs dF dU →
      refDefDt native_reflist_nil dU = true →
        refDefDt native_reflist_nil dF = true
  | SmtDatatype.null, dF, hImg, hRef => by
      simp [refDefDt] at hRef
  | SmtDatatype.sum c d, dF, hImg, hRef => by
      rcases hImg with ⟨cF, dF', rfl, hc, hd⟩
      have hp : refDefDtc native_reflist_nil c = true ∨
          refDefDt native_reflist_nil d = true := by
        simpa [refDefDt, Bool.or_eq_true] using hRef
      rcases hp with hHead | hTail
      · simp [refDefDt, Bool.or_eq_true,
          refDef_img_dtc refs c cF hc hHead]
      · simp [refDefDt, Bool.or_eq_true,
          refDef_img_dt refs d dF' hd hTail]

end

/-! The converse image fact keeps substituted references as explicit
obligations.  If a folded image has a reference-free default path, then its
raw source has the same path once every name that the image was allowed to
resolve is excused.  This is the direction needed when comparing two
different valid resolutions of one raw body. -/
mutual

private theorem refDef_img_inv_ty (refs : RefList) :
    ∀ (U F : SmtType), imgTy refs F U →
      refDefTy native_reflist_nil F = true → refDefTy refs U = true
  | SmtType.TypeRef r, F, hImg, hRef => by
      rcases hImg with rfl | ⟨hr, D, rfl⟩
      · simp [refDefTy, native_reflist_contains, native_reflist_nil] at hRef
      · simpa [refDefTy] using hr
  | SmtType.Datatype s D, F, hImg, hRef => by
      rcases hImg with ⟨DF, rfl, hBody⟩
      have hDF : refDefDt native_reflist_nil DF = true := by
        simpa [refDefTy] using hRef
      simpa [refDefTy] using refDef_img_inv_dt refs D DF hBody hDF
  | SmtType.None, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Bool, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Int, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Real, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.RegLan, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.BitVec w, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Map A B, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Set A, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Seq A, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.Char, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.USort u, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.FunType A B, F, hImg, hRef => by cases hImg; exact hRef
  | SmtType.DtcAppType A B, F, hImg, hRef => by cases hImg; exact hRef

private theorem refDef_img_inv_dtc (refs : RefList) :
    ∀ (cU cF : SmtDatatypeCons), imgDtc refs cF cU →
      refDefDtc native_reflist_nil cF = true → refDefDtc refs cU = true
  | SmtDatatypeCons.unit, cF, hImg, hRef => by
      cases hImg
      exact hRef
  | SmtDatatypeCons.cons T c, cF, hImg, hRef => by
      rcases hImg with ⟨TF, cF', rfl, hT, hc⟩
      have hp : refDefTy native_reflist_nil TF = true ∧
          refDefDtc native_reflist_nil cF' = true := by
        simpa [refDefDtc, Bool.and_eq_true] using hRef
      simp [refDefDtc, Bool.and_eq_true,
        refDef_img_inv_ty refs T TF hT hp.1,
        refDef_img_inv_dtc refs c cF' hc hp.2]

private theorem refDef_img_inv_dt (refs : RefList) :
    ∀ (dU dF : SmtDatatype), imgDt refs dF dU →
      refDefDt native_reflist_nil dF = true → refDefDt refs dU = true
  | SmtDatatype.null, dF, hImg, hRef => by
      cases hImg
      simpa [refDefDt] using hRef
  | SmtDatatype.sum c d, dF, hImg, hRef => by
      rcases hImg with ⟨cF, dF', rfl, hc, hd⟩
      have hp : refDefDtc native_reflist_nil cF = true ∨
          refDefDt native_reflist_nil dF' = true := by
        simpa [refDefDt, Bool.or_eq_true] using hRef
      rcases hp with hHead | hTail
      · simp [refDefDt, Bool.or_eq_true,
          refDef_img_inv_dtc refs c cF hc hHead]
      · simp [refDefDt, Bool.or_eq_true,
          refDef_img_inv_dt refs d dF' hd hTail]

end

/-! Positional images compose.  Keeping the same reference scope is enough:
if the intermediate image has already replaced a raw reference by a datatype,
its membership certificate is precisely the one needed by the composite. -/
mutual

private theorem img_trans_ty (refs : RefList) :
    ∀ (U M N : SmtType), imgTy refs M U → imgTy refs N M → imgTy refs N U
  | SmtType.TypeRef r, M, N, hUM, hMN => by
      rcases hUM with rfl | ⟨hr, E, rfl⟩
      · exact hMN
      · rcases hMN with ⟨EN, rfl, hBody⟩
        exact Or.inr ⟨hr, EN, rfl⟩
  | SmtType.Datatype s D, M, N, hUM, hMN => by
      rcases hUM with ⟨DM, rfl, hDM⟩
      rcases hMN with ⟨DN, rfl, hDN⟩
      exact ⟨DN, rfl, img_trans_dt refs D DM DN hDM hDN⟩
  | SmtType.None, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Bool, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Int, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Real, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.RegLan, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.BitVec w, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Map A B, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Set A, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Seq A, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.Char, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.USort u, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.FunType A B, M, N, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtType.DtcAppType A B, M, N, hUM, hMN => by
      cases hUM
      exact hMN

private theorem img_trans_dtc (refs : RefList) :
    ∀ (cU cM cN : SmtDatatypeCons), imgDtc refs cM cU →
      imgDtc refs cN cM → imgDtc refs cN cU
  | SmtDatatypeCons.unit, cM, cN, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtDatatypeCons.cons T c, cM, cN, hUM, hMN => by
      rcases hUM with ⟨TM, cM', rfl, hTM, hcM⟩
      rcases hMN with ⟨TN, cN', rfl, hTN, hcN⟩
      exact ⟨TN, cN', rfl, img_trans_ty refs T TM TN hTM hTN,
        img_trans_dtc refs c cM' cN' hcM hcN⟩

private theorem img_trans_dt (refs : RefList) :
    ∀ (dU dM dN : SmtDatatype), imgDt refs dM dU →
      imgDt refs dN dM → imgDt refs dN dU
  | SmtDatatype.null, dM, dN, hUM, hMN => by
      cases hUM
      exact hMN
  | SmtDatatype.sum c d, dM, dN, hUM, hMN => by
      rcases hUM with ⟨cM, dM', rfl, hcM, hdM⟩
      rcases hMN with ⟨cN, dN', rfl, hcN, hdN⟩
      exact ⟨cN, dN', rfl, img_trans_dtc refs c cM cN hcM hcN,
        img_trans_dt refs d dM' dN' hdM hdN⟩

end

/-! Lifting an image across a name absent from the raw source preserves the
image.  On a raw reference an exact folded datatype may become that same
reference, which is still an allowed image; at raw datatype nodes `noDt*`
rules out the only shape-changing case. -/
mutual

private theorem img_lift_no_dt_ty
    (refs : RefList) (s : native_String) (L : SmtDatatype) :
    ∀ (U F : SmtType), noDtTy s U = true → imgTy refs F U →
      imgTy refs (__smtx_type_lift s L F) U
  | SmtType.TypeRef r, F, _hNo, hImg => by
      rcases hImg with rfl | ⟨hr, E, rfl⟩
      · exact Or.inl (by simp [__smtx_type_lift])
      · by_cases hEq : (native_Teq
          (SmtType.Datatype s L) (SmtType.Datatype r E) = true)
        · have hParts : s = r ∧ L = E := by
            simpa [native_Teq] using hEq
          have hsr : r = s := hParts.1.symm
          subst r
          exact Or.inl (by
            simp [__smtx_type_lift, native_ite, hEq])
        · exact Or.inr ⟨hr, __smtx_dt_lift s L E, by
            simp [__smtx_type_lift, native_ite, hEq]⟩
  | SmtType.Datatype q D, F, hNo, hImg => by
      rcases hImg with ⟨DF, rfl, hBody⟩
      have hp : native_streq q s = false ∧ noDtDt s D = true := by
        simpa [noDtTy, native_and, native_not, Bool.and_eq_true] using hNo
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hp.1
      have hEq : native_Teq
          (SmtType.Datatype s L) (SmtType.Datatype q DF) = false := by
        cases h : native_Teq
            (SmtType.Datatype s L) (SmtType.Datatype q DF) <;>
          simp_all [native_Teq, native_streq]
      exact ⟨__smtx_dt_lift s L DF,
        by simp [__smtx_type_lift, native_ite, hEq],
        img_lift_no_dt_dt refs s L D DF hp.2 hBody⟩
  | SmtType.None, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Bool, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Int, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Real, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.RegLan, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.BitVec w, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Map A B, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Set A, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Seq A, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.Char, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.USort u, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.FunType A B, F, _hNo, hImg => by cases hImg; rfl
  | SmtType.DtcAppType A B, F, _hNo, hImg => by cases hImg; rfl

private theorem img_lift_no_dt_dtc
    (refs : RefList) (s : native_String) (L : SmtDatatype) :
    ∀ (cU cF : SmtDatatypeCons), noDtDtc s cU = true →
      imgDtc refs cF cU → imgDtc refs (__smtx_dtc_lift s L cF) cU
  | SmtDatatypeCons.unit, cF, _hNo, hImg => by
      cases hImg
      rfl
  | SmtDatatypeCons.cons T c, cF, hNo, hImg => by
      rcases hImg with ⟨TF, cF', rfl, hT, hc⟩
      have hp : noDtTy s T = true ∧ noDtDtc s c = true := by
        simpa [noDtDtc, native_and, Bool.and_eq_true] using hNo
      exact ⟨__smtx_type_lift s L TF, __smtx_dtc_lift s L cF',
        by simp [__smtx_dtc_lift],
        img_lift_no_dt_ty refs s L T TF hp.1 hT,
        img_lift_no_dt_dtc refs s L c cF' hp.2 hc⟩

private theorem img_lift_no_dt_dt
    (refs : RefList) (s : native_String) (L : SmtDatatype) :
    ∀ (dU dF : SmtDatatype), noDtDt s dU = true → imgDt refs dF dU →
      imgDt refs (__smtx_dt_lift s L dF) dU
  | SmtDatatype.null, dF, _hNo, hImg => by
      cases hImg
      rfl
  | SmtDatatype.sum c d, dF, hNo, hImg => by
      rcases hImg with ⟨cF, dF', rfl, hc, hd⟩
      have hp : noDtDtc s c = true ∧ noDtDt s d = true := by
        simpa [noDtDt, native_and, Bool.and_eq_true] using hNo
      exact ⟨__smtx_dtc_lift s L cF, __smtx_dt_lift s L dF',
        by simp [__smtx_dt_lift],
        img_lift_no_dt_dtc refs s L c cF hp.1 hc,
        img_lift_no_dt_dt refs s L d dF' hp.2 hd⟩

end

/-! ## Scoped positional images

Plain `imgTy/imgDt/imgDtc` deliberately only describe substitution: a raw
`TypeRef q` may become `Datatype q ...`, but a raw datatype node may not turn
back into a reference.  A canonical descent temporarily does exactly that
second operation.  Moreover, beneath another datatype binder its payload is
lifted again, so a single flat image relation cannot express the intermediate
state (this is the source of the duplicate-definition counterexamples).

`CtxImg* folds refs F U` is the scoped version.  `refs` has the usual meaning.
An entry `(q, D)` in `folds` additionally permits the *raw* node
`Datatype q D` to be represented by `TypeRef q`.  Descending through an
unfolded datatype records that exact raw node in the fold context.  The
relation therefore follows the capture-aware lift operation without losing
the raw body to which a later substitution must restore the node. -/

private abbrev FoldCtx := List (native_String × SmtDatatype)

/-! ## Definition-graph default paths

Capture-aware substitution can present the same finite definition graph with
different cycle cuts.  Concrete `refDef` paths therefore do not in general
replay position-for-position after a rotation.  The invariant which does not
depend on those cuts is a path in the raw definition graph.  Entering either
a named datatype node or a resolved reference removes that name from the
available definitions; hence every recursive premise is over a strictly
smaller environment when it follows a graph edge. -/

private def eraseFoldName (q : native_String) : FoldCtx → FoldCtx
  | [] => []
  | (s, R) :: defs =>
      if native_streq q s = true then eraseFoldName q defs
      else (s, R) :: eraseFoldName q defs

private def FoldCtxSub (defsOld defsNew : FoldCtx) : Prop :=
  ∀ q R, (q, R) ∈ defsOld → (q, R) ∈ defsNew

private theorem eraseFoldName_mem
    (q s : native_String) (R : SmtDatatype) (defs : FoldCtx)
    (hne : native_streq q s = false) :
    (s, R) ∈ eraseFoldName q defs ↔ (s, R) ∈ defs := by
  induction defs with
  | nil => simp [eraseFoldName]
  | cons p defs ih =>
      rcases p with ⟨t, D⟩
      cases hqt : native_streq q t with
      | true =>
          have hneST : (s, R) ≠ (t, D) := by
            intro hEq
            injection hEq with hst _hRD
            subst t
            rw [hne] at hqt
            contradiction
          simp [eraseFoldName, hqt, ih, hneST]
      | false => simp [eraseFoldName, hqt, ih]

private theorem eraseFoldName_self_not_mem
    (q : native_String) (R : SmtDatatype) (defs : FoldCtx) :
    (q, R) ∉ eraseFoldName q defs := by
  induction defs with
  | nil => simp [eraseFoldName]
  | cons p defs ih =>
      rcases p with ⟨s, D⟩
      cases hqs : native_streq q s with
      | true => simp [eraseFoldName, hqs, ih]
      | false =>
          have hne : q ≠ s := by
            intro hEq
            subst s
            simp [native_streq] at hqs
          simp [eraseFoldName, hqs, ih, hne]

private theorem eraseFoldName_sub {defsOld defsNew : FoldCtx}
    (hSub : FoldCtxSub defsOld defsNew) (q : native_String) :
    FoldCtxSub (eraseFoldName q defsOld) (eraseFoldName q defsNew) := by
  intro s R hMem
  have hne : native_streq q s = false := by
    cases hqs : native_streq q s with
    | false => rfl
    | true =>
        have hEq : q = s := by simpa [native_streq] using hqs
        subst s
        exact absurd hMem (eraseFoldName_self_not_mem q R defsOld)
  rw [eraseFoldName_mem q s R defsOld hne] at hMem
  rw [eraseFoldName_mem q s R defsNew hne]
  exact hSub s R hMem

mutual

private inductive GraphDefTy : FoldCtx → SmtType → Prop where
  | ref {defs : FoldCtx} {q : native_String} {R : SmtDatatype} :
      (q, R) ∈ defs → GraphDefDt (eraseFoldName q defs) R →
      GraphDefTy defs (SmtType.TypeRef q)
  | dt {defs : FoldCtx} {q : native_String} {D : SmtDatatype} :
      GraphDefDt (eraseFoldName q defs) D →
      GraphDefTy defs (SmtType.Datatype q D)
  | atom {defs : FoldCtx} {T : SmtType}
      (hRef : ∀ q : native_String, T ≠ SmtType.TypeRef q)
      (hDt : ∀ (q : native_String) (D : SmtDatatype),
        T ≠ SmtType.Datatype q D)
      (hDef : refDefTy native_reflist_nil T = true) :
      GraphDefTy defs T

private inductive GraphDefDtc : FoldCtx → SmtDatatypeCons → Prop where
  | unit {defs : FoldCtx} : GraphDefDtc defs SmtDatatypeCons.unit
  | cons {defs : FoldCtx} {T : SmtType} {c : SmtDatatypeCons} :
      GraphDefTy defs T → GraphDefDtc defs c →
      GraphDefDtc defs (SmtDatatypeCons.cons T c)

private inductive GraphDefDt : FoldCtx → SmtDatatype → Prop where
  | head {defs : FoldCtx} {c : SmtDatatypeCons} {D : SmtDatatype} :
      GraphDefDtc defs c → GraphDefDt defs (SmtDatatype.sum c D)
  | tail {defs : FoldCtx} {c : SmtDatatypeCons} {D : SmtDatatype} :
      GraphDefDt defs D → GraphDefDt defs (SmtDatatype.sum c D)

end

mutual

private theorem graphDef_mono_ty {defsOld defsNew : FoldCtx}
    (hSub : FoldCtxSub defsOld defsNew) :
    ∀ {T : SmtType}, GraphDefTy defsOld T → GraphDefTy defsNew T
  | _, GraphDefTy.ref hMem hBody =>
      GraphDefTy.ref (hSub _ _ hMem)
        (graphDef_mono_dt (eraseFoldName_sub hSub _) hBody)
  | _, GraphDefTy.dt hBody =>
      GraphDefTy.dt (graphDef_mono_dt (eraseFoldName_sub hSub _) hBody)
  | _, GraphDefTy.atom hRef hDt hDef => GraphDefTy.atom hRef hDt hDef

private theorem graphDef_mono_dtc {defsOld defsNew : FoldCtx}
    (hSub : FoldCtxSub defsOld defsNew) :
    ∀ {c : SmtDatatypeCons}, GraphDefDtc defsOld c → GraphDefDtc defsNew c
  | _, GraphDefDtc.unit => GraphDefDtc.unit
  | _, GraphDefDtc.cons hT hc =>
      GraphDefDtc.cons (graphDef_mono_ty hSub hT)
        (graphDef_mono_dtc hSub hc)

private theorem graphDef_mono_dt {defsOld defsNew : FoldCtx}
    (hSub : FoldCtxSub defsOld defsNew) :
    ∀ {D : SmtDatatype}, GraphDefDt defsOld D → GraphDefDt defsNew D
  | _, GraphDefDt.head hc => GraphDefDt.head (graphDef_mono_dtc hSub hc)
  | _, GraphDefDt.tail hD => GraphDefDt.tail (graphDef_mono_dt hSub hD)

end

mutual

private def CtxImgTy (folds : FoldCtx) (refs : RefList)
    (F : SmtType) : SmtType → Prop
  | SmtType.TypeRef q =>
      F = SmtType.TypeRef q ∨
        (native_reflist_contains refs q = true ∧
          ∃ D, F = SmtType.Datatype q D)
  | SmtType.Datatype q D =>
      (((q, D) ∈ folds) ∧ F = SmtType.TypeRef q) ∨
        ∃ DF, F = SmtType.Datatype q DF ∧
          CtxImgDt ((q, D) :: folds) refs DF D
  | U => F = U

private def CtxImgDtc (folds : FoldCtx) (refs : RefList)
    (cF : SmtDatatypeCons) : SmtDatatypeCons → Prop
  | SmtDatatypeCons.unit => cF = SmtDatatypeCons.unit
  | SmtDatatypeCons.cons T c =>
      ∃ TF cF', cF = SmtDatatypeCons.cons TF cF' ∧
        CtxImgTy folds refs TF T ∧ CtxImgDtc folds refs cF' c

private def CtxImgDt (folds : FoldCtx) (refs : RefList)
    (dF : SmtDatatype) : SmtDatatype → Prop
  | SmtDatatype.null => dF = SmtDatatype.null
  | SmtDatatype.sum c d =>
      ∃ cF dF', dF = SmtDatatype.sum cF dF' ∧
        CtxImgDtc folds refs cF c ∧ CtxImgDt folds refs dF' d

end

/-! `CtxImg*` deliberately forgets which definition supplied the body at a
resolved reference.  That is enough for positional-image arguments, but not
for comparing two resolutions: a default path may enter that supplied body.

`SemImg* defs folds F U` is the proof-relevant refinement used for that
comparison.  `defs` is the raw definition environment.  `folds` contains the
datatype binders which are currently closed, so a reference to a folded name
stays a reference.  Otherwise a name present in `defs` must be represented by
a datatype whose body is recursively an image of that definition.  This is
still relational--different valid histories may produce different bodies--
but it no longer permits an unrelated body at a resolved reference. -/

private def FoldBound (folds : FoldCtx) (q : native_String) : Prop :=
  ∃ D : SmtDatatype, (q, D) ∈ folds

private def FoldDefined (defs : FoldCtx) (q : native_String) : Prop :=
  ∃ D : SmtDatatype, (q, D) ∈ defs

private def FoldFunctional (defs : FoldCtx) : Prop :=
  ∀ q D E, (q, D) ∈ defs → (q, E) ∈ defs → D = E

mutual

private inductive SemImgTy (defs : FoldCtx) :
    FoldCtx → SmtType → SmtType → Prop where
  | boundRef {q : native_String} :
      FoldBound folds q →
      SemImgTy defs folds (SmtType.TypeRef q) (SmtType.TypeRef q)
  | openRef {q : native_String} :
      (¬ FoldBound folds q) → (¬ FoldDefined defs q) →
      SemImgTy defs folds (SmtType.TypeRef q) (SmtType.TypeRef q)
  | resolvedRef {q : native_String} {R B : SmtDatatype} :
      (¬ FoldBound folds q) → (q, R) ∈ defs →
      SemImgDt defs ((q, R) :: folds) B R →
      SemImgTy defs folds (SmtType.Datatype q B) (SmtType.TypeRef q)
  | foldedDt {q : native_String} {D : SmtDatatype} :
      (q, D) ∈ folds →
      SemImgTy defs folds (SmtType.TypeRef q) (SmtType.Datatype q D)
  | datatype {q : native_String} {D B : SmtDatatype} :
      (q, D) ∉ folds →
      SemImgDt defs ((q, D) :: folds) B D →
      SemImgTy defs folds (SmtType.Datatype q B) (SmtType.Datatype q D)
  | same {U : SmtType}
      (hRef : ∀ q : native_String, U ≠ SmtType.TypeRef q)
      (hDt : ∀ (q : native_String) (D : SmtDatatype),
        U ≠ SmtType.Datatype q D) :
      SemImgTy defs folds U U

private inductive SemImgDtc (defs : FoldCtx) :
    FoldCtx → SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : SemImgDtc defs folds SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TF TU : SmtType} {cF cU : SmtDatatypeCons} :
      SemImgTy defs folds TF TU → SemImgDtc defs folds cF cU →
      SemImgDtc defs folds (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU)

private inductive SemImgDt (defs : FoldCtx) :
    FoldCtx → SmtDatatype → SmtDatatype → Prop where
  | null : SemImgDt defs folds SmtDatatype.null SmtDatatype.null
  | sum {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype} :
      SemImgDtc defs folds cF cU → SemImgDt defs folds dF dU →
      SemImgDt defs folds (SmtDatatype.sum cF dF)
        (SmtDatatype.sum cU dU)

end

/-! A finite default path can be replayed in any semantic image whose raw
environment extends the old one.  The only non-structural case is a raw
reference.  There the old path contains a strict subpath through the old
definition body; environment functionality identifies the new definition,
and recursion continues on that strict subpath. -/

mutual

private theorem semImg_defPath_ty
    {defsOld defsNew : FoldCtx}
    (hSub : ∀ p, p ∈ defsOld → p ∈ defsNew)
    (hFun : FoldFunctional defsNew) :
    ∀ {folds : FoldCtx} {U TOld TNew : SmtType},
      SemImgTy defsOld folds TOld U →
      SemImgTy defsNew folds TNew U →
      DefPathTy native_reflist_nil TOld →
      DefPathTy native_reflist_nil TNew := by
  intro folds U TOld TNew hOld hNew hPath
  cases hPath with
  | ref h =>
      simp [native_reflist_contains, native_reflist_nil] at h
  | atom hNotRef hNotDt hDef =>
      cases hOld with
      | boundRef _ => exact absurd rfl (hNotRef _)
      | openRef _ _ => exact absurd rfl (hNotRef _)
      | resolvedRef _ _ _ => exact absurd rfl (hNotDt _ _)
      | foldedDt _ => exact absurd rfl (hNotRef _)
      | datatype _ _ => exact absurd rfl (hNotDt _ _)
      | same hOldNotRef hOldNotDt =>
          cases hNew with
          | boundRef _ => exact absurd rfl (hOldNotRef _)
          | openRef _ _ => exact absurd rfl (hOldNotRef _)
          | resolvedRef _ _ _ => exact absurd rfl (hOldNotRef _)
          | foldedDt _ => exact absurd rfl (hOldNotDt _ _)
          | datatype _ _ => exact absurd rfl (hOldNotDt _ _)
          | same _ _ => exact DefPathTy.atom hNotRef hNotDt hDef
  | @dt sOld dOld hBody =>
      cases hOld with
      | @resolvedRef _ q ROld BOld hNotBound hROld hBOld =>
          cases hNew with
          | boundRef hBound => exact absurd hBound hNotBound
          | openRef _ hNoDef =>
              exact absurd ⟨ROld, hSub (sOld, ROld) hROld⟩ hNoDef
          | @resolvedRef _ _ RNew BNew _ hRNew hBNew =>
              have hRaw : ROld = RNew :=
                hFun sOld ROld RNew (hSub (sOld, ROld) hROld) hRNew
              subst RNew
              exact DefPathTy.dt
                (semImg_defPath_dt
                  (folds := (sOld, ROld) :: folds) hSub hFun
                  hBOld hBNew hBody)
          | same hRef _ => exact absurd rfl (hRef sOld)
      | @datatype _ q D BOld hNotMem hBOld =>
          cases hNew with
          | foldedDt hMem => exact absurd hMem hNotMem
          | @datatype _ _ _ BNew _ hBNew =>
              exact DefPathTy.dt
                (semImg_defPath_dt
                  (folds := (sOld, D) :: folds) hSub hFun
                  hBOld hBNew hBody)
          | same _ hDt => exact absurd rfl (hDt sOld D)
      | same _ hDt => exact absurd rfl (hDt sOld dOld)

private theorem semImg_defPath_dtc
    {defsOld defsNew : FoldCtx}
    (hSub : ∀ p, p ∈ defsOld → p ∈ defsNew)
    (hFun : FoldFunctional defsNew) :
    ∀ {folds : FoldCtx} {cU cOld cNew : SmtDatatypeCons},
      SemImgDtc defsOld folds cOld cU →
      SemImgDtc defsNew folds cNew cU →
      DefPathDtc native_reflist_nil cOld →
      DefPathDtc native_reflist_nil cNew := by
  intro folds cU cOld cNew hOld hNew hPath
  cases hPath with
  | unit =>
      cases hOld
      cases hNew
      exact DefPathDtc.unit
  | cons hT hc =>
      cases hOld with
      | cons hTOld hcOld =>
          cases hNew with
          | cons hTNew hcNew =>
              exact DefPathDtc.cons
                (semImg_defPath_ty (folds := folds) hSub hFun
                  hTOld hTNew hT)
                (semImg_defPath_dtc (folds := folds) hSub hFun
                  hcOld hcNew hc)

private theorem semImg_defPath_dt
    {defsOld defsNew : FoldCtx}
    (hSub : ∀ p, p ∈ defsOld → p ∈ defsNew)
    (hFun : FoldFunctional defsNew) :
    ∀ {folds : FoldCtx} {dU dOld dNew : SmtDatatype},
      SemImgDt defsOld folds dOld dU →
      SemImgDt defsNew folds dNew dU →
      DefPathDt native_reflist_nil dOld →
      DefPathDt native_reflist_nil dNew := by
  intro folds dU dOld dNew hOld hNew hPath
  cases hPath with
  | head hc =>
      cases hOld with
      | sum hcOld hdOld =>
          cases hNew with
          | sum hcNew hdNew =>
              exact DefPathDt.head
                (semImg_defPath_dtc (folds := folds) hSub hFun
                  hcOld hcNew hc)
  | tail hd =>
      cases hOld with
      | sum hcOld hdOld =>
          cases hNew with
          | sum hcNew hdNew =>
              exact DefPathDt.tail
                (semImg_defPath_dt (folds := folds) hSub hFun
                  hdOld hdNew hd)

end

private theorem semImg_refDef_dt
    {defsOld defsNew folds : FoldCtx}
    (hSub : ∀ p, p ∈ defsOld → p ∈ defsNew)
    (hFun : FoldFunctional defsNew)
    {U DOld DNew : SmtDatatype}
    (hOld : SemImgDt defsOld folds DOld U)
    (hNew : SemImgDt defsNew folds DNew U) :
    refDefDt native_reflist_nil DOld = true →
      refDefDt native_reflist_nil DNew = true := by
  intro hDef
  exact refDef_of_defPathDt
    (semImg_defPath_dt (folds := folds) hSub hFun hOld hNew
      (defPathDt_of_refDef native_reflist_nil DOld hDef))

/-! Semantic images depend on a fold context only through membership. -/
mutual

private theorem semImg_folds_congr_ty {defs : FoldCtx} :
    ∀ {folds folds' : FoldCtx} {F U : SmtType},
      (∀ p, p ∈ folds ↔ p ∈ folds') →
      SemImgTy defs folds F U → SemImgTy defs folds' F U
  | _, _, _, _, hMem, SemImgTy.boundRef hBound =>
      SemImgTy.boundRef (by
        rcases hBound with ⟨D, hD⟩
        exact ⟨D, (hMem ( _ , D)).mp hD⟩)
  | _, _, _, _, hMem, SemImgTy.openRef hNotBound hNoDef =>
      SemImgTy.openRef
        (by
          intro hBound
          rcases hBound with ⟨D, hD⟩
          exact hNotBound ⟨D, (hMem (_, D)).mpr hD⟩)
        hNoDef
  | _, _, _, _, hMem,
      @SemImgTy.resolvedRef _ _ q R B hNotBound hR hBody =>
      SemImgTy.resolvedRef
        (by
          intro hBound
          rcases hBound with ⟨D, hD⟩
          exact hNotBound ⟨D, (hMem (_, D)).mpr hD⟩)
        hR
        (semImg_folds_congr_dt
          (fun p => by
            simp only [List.mem_cons]
            constructor <;> intro hp
            · exact hp.elim Or.inl (fun h => Or.inr ((hMem p).mp h))
            · exact hp.elim Or.inl (fun h => Or.inr ((hMem p).mpr h)))
          hBody)
  | _, _, _, _, hMem, SemImgTy.foldedDt hFold =>
      SemImgTy.foldedDt ((hMem _).mp hFold)
  | _, _, _, _, hMem, @SemImgTy.datatype _ _ q D B hNotFold hBody =>
      SemImgTy.datatype
        (fun h => hNotFold ((hMem (q, D)).mpr h))
        (semImg_folds_congr_dt
          (fun p => by
            simp only [List.mem_cons]
            constructor <;> intro hp
            · exact hp.elim Or.inl (fun h => Or.inr ((hMem p).mp h))
            · exact hp.elim Or.inl (fun h => Or.inr ((hMem p).mpr h)))
          hBody)
  | _, _, _, _, _hMem, SemImgTy.same hRef hDt => SemImgTy.same hRef hDt

private theorem semImg_folds_congr_dtc {defs : FoldCtx} :
    ∀ {folds folds' : FoldCtx} {cF cU : SmtDatatypeCons},
      (∀ p, p ∈ folds ↔ p ∈ folds') →
      SemImgDtc defs folds cF cU → SemImgDtc defs folds' cF cU
  | _, _, _, _, _hMem, SemImgDtc.unit => SemImgDtc.unit
  | _, _, _, _, hMem, SemImgDtc.cons hT hc =>
      SemImgDtc.cons (semImg_folds_congr_ty hMem hT)
        (semImg_folds_congr_dtc hMem hc)

private theorem semImg_folds_congr_dt {defs : FoldCtx} :
    ∀ {folds folds' : FoldCtx} {dF dU : SmtDatatype},
      (∀ p, p ∈ folds ↔ p ∈ folds') →
      SemImgDt defs folds dF dU → SemImgDt defs folds' dF dU
  | _, _, _, _, _hMem, SemImgDt.null => SemImgDt.null
  | _, _, _, _, hMem, SemImgDt.sum hc hd =>
      SemImgDt.sum (semImg_folds_congr_dtc hMem hc)
        (semImg_folds_congr_dt hMem hd)

end

/-! Reflexivity holds when every available definition is currently folded
and every folded datatype is strictly above the raw object being related.
The size side condition rules out the only shape-changing alternative at a
raw datatype node. -/

mutual

private theorem semImg_refl_ty (defs folds : FoldCtx) :
    ∀ U : SmtType,
      (∀ q, FoldDefined defs q → FoldBound folds q) →
      (∀ q D, (q, D) ∈ folds →
        sizeOf U < sizeOf (SmtType.Datatype q D)) →
      SemImgTy defs folds U U
  | SmtType.TypeRef q, hBound, _hAbove => by
      by_cases hb : FoldBound folds q
      · exact SemImgTy.boundRef hb
      · apply SemImgTy.openRef hb
        intro hd
        exact hb (hBound q hd)
  | SmtType.Datatype q D, hBound, hAbove => by
      have hNotMem : (q, D) ∉ folds := by
        intro hMem
        have hlt := hAbove q D hMem
        simp at hlt
      exact SemImgTy.datatype hNotMem
        (semImg_refl_dt defs ((q, D) :: folds) D
          (by
            intro r hd
            by_cases hrq : r = q
            · subst r
              exact ⟨D, by simp⟩
            · rcases hd with ⟨E, hE⟩
              have hb := hBound r ⟨E, hE⟩
              rcases hb with ⟨B, hB⟩
              exact ⟨B, by simp [hB]⟩)
          (by
            intro r E hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with hEq | hMem
            · cases hEq
              simp
              omega
            · have hlt := hAbove r E hMem
              simp at hlt ⊢
              omega))
  | SmtType.None, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Bool, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Int, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Real, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.RegLan, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.BitVec w, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Map A B, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Set A, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Seq A, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.Char, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.USort u, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.FunType A B, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)
  | SmtType.DtcAppType A B, _hBound, _hAbove =>
      SemImgTy.same (fun _ h => by cases h) (fun _ _ h => by cases h)

private theorem semImg_refl_dtc (defs folds : FoldCtx) :
    ∀ c : SmtDatatypeCons,
      (∀ q, FoldDefined defs q → FoldBound folds q) →
      (∀ q D, (q, D) ∈ folds →
        sizeOf c < sizeOf (SmtType.Datatype q D)) →
      SemImgDtc defs folds c c
  | SmtDatatypeCons.unit, _hBound, _hAbove => SemImgDtc.unit
  | SmtDatatypeCons.cons T c, hBound, hAbove =>
      SemImgDtc.cons
        (semImg_refl_ty defs folds T hBound (by
          intro q D hMem
          have hlt := hAbove q D hMem
          simp at hlt ⊢
          omega))
        (semImg_refl_dtc defs folds c hBound (by
          intro q D hMem
          have hlt := hAbove q D hMem
          simp at hlt ⊢
          omega))

private theorem semImg_refl_dt (defs folds : FoldCtx) :
    ∀ d : SmtDatatype,
      (∀ q, FoldDefined defs q → FoldBound folds q) →
      (∀ q D, (q, D) ∈ folds →
        sizeOf d < sizeOf (SmtType.Datatype q D)) →
      SemImgDt defs folds d d
  | SmtDatatype.null, _hBound, _hAbove => SemImgDt.null
  | SmtDatatype.sum c d, hBound, hAbove =>
      SemImgDt.sum
        (semImg_refl_dtc defs folds c hBound (by
          intro q D hMem
          have hlt := hAbove q D hMem
          simp at hlt ⊢
          omega))
        (semImg_refl_dt defs folds d hBound (by
          intro q D hMem
          have hlt := hAbove q D hMem
          simp at hlt ⊢
          omega))

end

/-! Forgetting the body provenance yields the ordinary scoped image. -/
mutual

private theorem semImg_to_ctx_ty
    {defs : FoldCtx} {refs : RefList}
    (hDefs : ∀ q R, (q, R) ∈ defs →
      native_reflist_contains refs q = true) :
    ∀ {folds : FoldCtx} {F U : SmtType},
      SemImgTy defs folds F U → CtxImgTy folds refs F U
  | _, _, _, SemImgTy.boundRef _ => Or.inl rfl
  | _, _, _, SemImgTy.openRef _ _ => Or.inl rfl
  | _, _, _, @SemImgTy.resolvedRef _ _ q R B _ hR _ =>
      Or.inr ⟨hDefs q R hR, B, rfl⟩
  | _, _, _, SemImgTy.foldedDt hMem => Or.inl ⟨hMem, rfl⟩
  | _, _, _, SemImgTy.datatype _ hBody =>
      Or.inr ⟨_, rfl, semImg_to_ctx_dt hDefs hBody⟩
  | _, _, _, @SemImgTy.same _ _ U hRef hDt => by
      cases U <;> first
        | rfl
        | exact absurd rfl (hRef _)
        | exact absurd rfl (hDt _ _)

private theorem semImg_to_ctx_dtc
    {defs : FoldCtx} {refs : RefList}
    (hDefs : ∀ q R, (q, R) ∈ defs →
      native_reflist_contains refs q = true) :
    ∀ {folds : FoldCtx} {cF cU : SmtDatatypeCons},
      SemImgDtc defs folds cF cU → CtxImgDtc folds refs cF cU
  | _, _, _, SemImgDtc.unit => rfl
  | _, _, _, SemImgDtc.cons hT hc =>
      ⟨_, _, rfl, semImg_to_ctx_ty hDefs hT,
        semImg_to_ctx_dtc hDefs hc⟩

private theorem semImg_to_ctx_dt
    {defs : FoldCtx} {refs : RefList}
    (hDefs : ∀ q R, (q, R) ∈ defs →
      native_reflist_contains refs q = true) :
    ∀ {folds : FoldCtx} {dF dU : SmtDatatype},
      SemImgDt defs folds dF dU → CtxImgDt folds refs dF dU
  | _, _, _, SemImgDt.null => rfl
  | _, _, _, SemImgDt.sum hc hd =>
      ⟨_, _, rfl, semImg_to_ctx_dtc hDefs hc,
        semImg_to_ctx_dt hDefs hd⟩

end

mutual

private theorem ctxImg_refl_ty (folds : FoldCtx) (refs : RefList) :
    ∀ T : SmtType, CtxImgTy folds refs T T
  | SmtType.TypeRef q => Or.inl rfl
  | SmtType.Datatype q D =>
      Or.inr ⟨D, rfl, ctxImg_refl_dt ((q, D) :: folds) refs D⟩
  | SmtType.None => rfl
  | SmtType.Bool => rfl
  | SmtType.Int => rfl
  | SmtType.Real => rfl
  | SmtType.RegLan => rfl
  | SmtType.BitVec w => rfl
  | SmtType.Map A B => rfl
  | SmtType.Set A => rfl
  | SmtType.Seq A => rfl
  | SmtType.Char => rfl
  | SmtType.USort u => rfl
  | SmtType.FunType A B => rfl
  | SmtType.DtcAppType A B => rfl

private theorem ctxImg_refl_dtc (folds : FoldCtx) (refs : RefList) :
    ∀ c : SmtDatatypeCons, CtxImgDtc folds refs c c
  | SmtDatatypeCons.unit => rfl
  | SmtDatatypeCons.cons T c =>
      ⟨T, c, rfl, ctxImg_refl_ty folds refs T,
        ctxImg_refl_dtc folds refs c⟩

private theorem ctxImg_refl_dt (folds : FoldCtx) (refs : RefList) :
    ∀ d : SmtDatatype, CtxImgDt folds refs d d
  | SmtDatatype.null => rfl
  | SmtDatatype.sum c d =>
      ⟨c, d, rfl, ctxImg_refl_dtc folds refs c,
        ctxImg_refl_dt folds refs d⟩

end

/-! Ordinary substitution images are scoped images in every ambient fold
context.  This is used for a freshly appended entry, whose payload is produced
by applying the already-built prefix chain to its raw body. -/
mutual

private theorem ctxImg_of_img_ty (folds : FoldCtx) (refs : RefList) :
    ∀ (U F : SmtType), imgTy refs F U → CtxImgTy folds refs F U
  | SmtType.TypeRef q, F, h => h
  | SmtType.Datatype q D, F, h => by
      rcases h with ⟨DF, rfl, hBody⟩
      exact Or.inr ⟨DF, rfl,
        ctxImg_of_img_dt ((q, D) :: folds) refs D DF hBody⟩
  | SmtType.None, F, h => h
  | SmtType.Bool, F, h => h
  | SmtType.Int, F, h => h
  | SmtType.Real, F, h => h
  | SmtType.RegLan, F, h => h
  | SmtType.BitVec w, F, h => h
  | SmtType.Map A B, F, h => h
  | SmtType.Set A, F, h => h
  | SmtType.Seq A, F, h => h
  | SmtType.Char, F, h => h
  | SmtType.USort u, F, h => h
  | SmtType.FunType A B, F, h => h
  | SmtType.DtcAppType A B, F, h => h

private theorem ctxImg_of_img_dtc (folds : FoldCtx) (refs : RefList) :
    ∀ (cU cF : SmtDatatypeCons), imgDtc refs cF cU →
      CtxImgDtc folds refs cF cU
  | SmtDatatypeCons.unit, cF, h => h
  | SmtDatatypeCons.cons T c, cF, h => by
      rcases h with ⟨TF, cF', rfl, hT, hc⟩
      exact ⟨TF, cF', rfl, ctxImg_of_img_ty folds refs T TF hT,
        ctxImg_of_img_dtc folds refs c cF' hc⟩

private theorem ctxImg_of_img_dt (folds : FoldCtx) (refs : RefList) :
    ∀ (dU dF : SmtDatatype), imgDt refs dF dU →
      CtxImgDt folds refs dF dU
  | SmtDatatype.null, dF, h => h
  | SmtDatatype.sum c d, dF, h => by
      rcases h with ⟨cF, dF', rfl, hc, hd⟩
      exact ⟨cF, dF', rfl, ctxImg_of_img_dtc folds refs c cF hc,
        ctxImg_of_img_dt folds refs d dF' hd⟩

end


mutual

private theorem ctxImg_mono_ty
    {folds folds' : FoldCtx} {refs refs' : RefList}
    (hFolds : ∀ p, p ∈ folds → p ∈ folds')
    (hRefs : ∀ q, native_reflist_contains refs q = true →
      native_reflist_contains refs' q = true) :
    ∀ (U F : SmtType), CtxImgTy folds refs F U →
      CtxImgTy folds' refs' F U
  | SmtType.TypeRef q, F, h => by
      rcases h with hEq | ⟨hq, D, hEq⟩
      · exact Or.inl hEq
      · exact Or.inr ⟨hRefs q hq, D, hEq⟩
  | SmtType.Datatype q D, F, h => by
      rcases h with ⟨hMem, hEq⟩ | ⟨DF, hEq, hBody⟩
      · exact Or.inl ⟨hFolds (q, D) hMem, hEq⟩
      · exact Or.inr ⟨DF, hEq,
          ctxImg_mono_dt
            (fun p hp => by
              simp only [List.mem_cons] at hp ⊢
              exact hp.elim Or.inl (fun h => Or.inr (hFolds p h)))
            hRefs D DF hBody⟩
  | SmtType.None, F, h => h
  | SmtType.Bool, F, h => h
  | SmtType.Int, F, h => h
  | SmtType.Real, F, h => h
  | SmtType.RegLan, F, h => h
  | SmtType.BitVec w, F, h => h
  | SmtType.Map A B, F, h => h
  | SmtType.Set A, F, h => h
  | SmtType.Seq A, F, h => h
  | SmtType.Char, F, h => h
  | SmtType.USort u, F, h => h
  | SmtType.FunType A B, F, h => h
  | SmtType.DtcAppType A B, F, h => h

private theorem ctxImg_mono_dtc
    {folds folds' : FoldCtx} {refs refs' : RefList}
    (hFolds : ∀ p, p ∈ folds → p ∈ folds')
    (hRefs : ∀ q, native_reflist_contains refs q = true →
      native_reflist_contains refs' q = true) :
    ∀ (cU cF : SmtDatatypeCons), CtxImgDtc folds refs cF cU →
      CtxImgDtc folds' refs' cF cU
  | SmtDatatypeCons.unit, cF, h => h
  | SmtDatatypeCons.cons T c, cF, h => by
      rcases h with ⟨TF, cF', hEq, hT, hc⟩
      exact ⟨TF, cF', hEq, ctxImg_mono_ty hFolds hRefs T TF hT,
        ctxImg_mono_dtc hFolds hRefs c cF' hc⟩

private theorem ctxImg_mono_dt
    {folds folds' : FoldCtx} {refs refs' : RefList}
    (hFolds : ∀ p, p ∈ folds → p ∈ folds')
    (hRefs : ∀ q, native_reflist_contains refs q = true →
      native_reflist_contains refs' q = true) :
    ∀ (dU dF : SmtDatatype), CtxImgDt folds refs dF dU →
      CtxImgDt folds' refs' dF dU
  | SmtDatatype.null, dF, h => h
  | SmtDatatype.sum c d, dF, h => by
      rcases h with ⟨cF, dF', hEq, hc, hd⟩
      exact ⟨cF, dF', hEq, ctxImg_mono_dtc hFolds hRefs c cF hc,
        ctxImg_mono_dt hFolds hRefs d dF' hd⟩

end


private theorem noStrayTy_same_name_body
    (s : native_String) (X D : SmtDatatype)
    (h : noStrayTy s X (SmtType.Datatype s D) = true) :
    D = X := by
  by_cases hEq : native_Teq
      (SmtType.Datatype s X) (SmtType.Datatype s D) = true
  · have hp : s = s ∧ X = D := by simpa [native_Teq] using hEq
    exact hp.2.symm
  · exfalso
    simpa [noStrayTy, native_ite, hEq, native_streq, native_and,
      native_not] using h


mutual

/-- Lifting the folded side adds exactly one raw datatype to the fold scope.
`noStray` supplies the raw-body identity when an exact contextual image is
actually folded. -/
private theorem ctxImg_lift_ty
    (folds : FoldCtx) (refs : RefList)
    (s : native_String) (X Y : SmtDatatype)
    (hTargetStray : noStrayDt s X X = true) :
    ∀ (U F : SmtType), noStrayTy s X U = true →
      CtxImgTy folds refs F U →
      CtxImgTy ((s, X) :: folds) refs (__smtx_type_lift s Y F) U
  | SmtType.TypeRef q, F, _hStray, hImg => by
      rcases hImg with rfl | ⟨hq, D, rfl⟩
      · exact Or.inl (by simp [__smtx_type_lift])
      · by_cases hFold : native_Teq
            (SmtType.Datatype s Y) (SmtType.Datatype q D) = true
        · have hp : s = q ∧ Y = D := by simpa [native_Teq] using hFold
          obtain ⟨rfl, rfl⟩ := hp
          exact Or.inl (by simp [__smtx_type_lift, native_ite, native_Teq])
        · exact Or.inr ⟨hq, __smtx_dt_lift s Y D, by
            simp [__smtx_type_lift, native_ite, hFold]⟩
  | SmtType.Datatype q D, F, hStray, hImg => by
      rcases hImg with ⟨hMem, rfl⟩ | ⟨DF, rfl, hBody⟩
      · exact Or.inl ⟨by simp only [List.mem_cons]; exact Or.inr hMem,
          by simp [__smtx_type_lift]⟩
      · by_cases hFold : native_Teq
            (SmtType.Datatype s Y) (SmtType.Datatype q DF) = true
        · have hp : s = q ∧ Y = DF := by simpa [native_Teq] using hFold
          obtain ⟨rfl, rfl⟩ := hp
          have hDX : D = X := noStrayTy_same_name_body s X D hStray
          subst D
          exact Or.inl ⟨by simp, by
            simp [__smtx_type_lift, native_ite, native_Teq]⟩
        · refine Or.inr ⟨__smtx_dt_lift s Y DF, by
            simp [__smtx_type_lift, native_ite, hFold], ?_⟩
          have hBodyStray : noStrayDt s X D = true := by
            by_cases hRaw : native_Teq
                (SmtType.Datatype s X) (SmtType.Datatype q D) = true
            · have hp : s = q ∧ X = D := by simpa [native_Teq] using hRaw
              obtain ⟨rfl, rfl⟩ := hp
              exact hTargetStray
            · have hqs : native_streq q s = false := by
                cases hqs : native_streq q s with
                | false => rfl
                | true =>
                    have heq : q = s := by simpa [native_streq] using hqs
                    subst q
                    exfalso
                    simp [noStrayTy, native_ite, hRaw, native_streq,
                      native_and, native_not] at hStray
              have hsq : native_streq s q = false := by
                simpa [native_streq, eq_comm] using hqs
              simpa [noStrayTy, native_ite, hRaw, hqs, hsq,
                native_and, native_not] using hStray
          have hRec := ctxImg_lift_dt ((q, D) :: folds) refs s X Y hTargetStray
            D DF hBodyStray hBody
          exact ctxImg_mono_dt
            (folds := (s, X) :: (q, D) :: folds)
            (folds' := (q, D) :: (s, X) :: folds)
            (refs := refs) (refs' := refs)
            (by
              intro p hp
              simp only [List.mem_cons] at hp ⊢
              rcases hp with rfl | rfl | hp
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl rfl
              · exact Or.inr (Or.inr hp))
            (fun _ h => h) D _ hRec
  | SmtType.None, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Bool, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Int, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Real, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.RegLan, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.BitVec w, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Map A B, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Set A, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Seq A, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.Char, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.USort u, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.FunType A B, F, _hStray, hImg => by cases hImg; rfl
  | SmtType.DtcAppType A B, F, _hStray, hImg => by cases hImg; rfl

private theorem ctxImg_lift_dtc
    (folds : FoldCtx) (refs : RefList)
    (s : native_String) (X Y : SmtDatatype)
    (hTargetStray : noStrayDt s X X = true) :
    ∀ (cU cF : SmtDatatypeCons), noStrayDtc s X cU = true →
      CtxImgDtc folds refs cF cU →
      CtxImgDtc ((s, X) :: folds) refs (__smtx_dtc_lift s Y cF) cU
  | SmtDatatypeCons.unit, cF, _hStray, hImg => by cases hImg; rfl
  | SmtDatatypeCons.cons T c, cF, hStray, hImg => by
      rcases hImg with ⟨TF, cF', rfl, hT, hc⟩
      have hp : noStrayTy s X T = true ∧ noStrayDtc s X c = true := by
        simpa [noStrayDtc, native_and, Bool.and_eq_true] using hStray
      exact ⟨_, _, rfl,
        ctxImg_lift_ty folds refs s X Y hTargetStray T TF hp.1 hT,
        ctxImg_lift_dtc folds refs s X Y hTargetStray c cF' hp.2 hc⟩

private theorem ctxImg_lift_dt
    (folds : FoldCtx) (refs : RefList)
    (s : native_String) (X Y : SmtDatatype)
    (hTargetStray : noStrayDt s X X = true) :
    ∀ (dU dF : SmtDatatype), noStrayDt s X dU = true →
      CtxImgDt folds refs dF dU →
      CtxImgDt ((s, X) :: folds) refs (__smtx_dt_lift s Y dF) dU
  | SmtDatatype.null, dF, _hStray, hImg => by cases hImg; rfl
  | SmtDatatype.sum c d, dF, hStray, hImg => by
      rcases hImg with ⟨cF, dF', rfl, hc, hd⟩
      have hp : noStrayDtc s X c = true ∧ noStrayDt s X d = true := by
        simpa [noStrayDt, native_and, Bool.and_eq_true] using hStray
      exact ⟨_, _, rfl,
        ctxImg_lift_dtc folds refs s X Y hTargetStray c cF hp.1 hc,
        ctxImg_lift_dt folds refs s X Y hTargetStray d dF' hp.2 hd⟩

end

/-! Fold scopes disappear at the outer boundary.  More generally, if every
raw datatype recorded in the scope is strictly larger than the current raw
subtree, the fold alternative is impossible.  Adding the current datatype
when descending into its body preserves exactly that size invariant. -/
mutual

private theorem ctxImg_to_img_ty
    (folds : FoldCtx) (refs : RefList) :
    ∀ (U F : SmtType),
      (∀ q D, (q, D) ∈ folds → sizeOf U < sizeOf (SmtType.Datatype q D)) →
      CtxImgTy folds refs F U → imgTy refs F U
  | SmtType.TypeRef q, F, _hAbove, hImg => hImg
  | SmtType.Datatype q D, F, hAbove, hImg => by
      rcases hImg with ⟨hMem, hEq⟩ | ⟨DF, hEq, hBody⟩
      · have hlt := hAbove q D hMem
        simp at hlt
      · exact ⟨DF, hEq, ctxImg_to_img_dt ((q, D) :: folds) refs D DF
          (by
            intro r E hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with hEq | hMem
            · cases hEq
              simp
              omega
            · have hlt := hAbove r E hMem
              simp at hlt ⊢
              omega)
          hBody⟩
  | SmtType.None, F, _hAbove, hImg => hImg
  | SmtType.Bool, F, _hAbove, hImg => hImg
  | SmtType.Int, F, _hAbove, hImg => hImg
  | SmtType.Real, F, _hAbove, hImg => hImg
  | SmtType.RegLan, F, _hAbove, hImg => hImg
  | SmtType.BitVec w, F, _hAbove, hImg => hImg
  | SmtType.Map A B, F, _hAbove, hImg => hImg
  | SmtType.Set A, F, _hAbove, hImg => hImg
  | SmtType.Seq A, F, _hAbove, hImg => hImg
  | SmtType.Char, F, _hAbove, hImg => hImg
  | SmtType.USort u, F, _hAbove, hImg => hImg
  | SmtType.FunType A B, F, _hAbove, hImg => hImg
  | SmtType.DtcAppType A B, F, _hAbove, hImg => hImg

private theorem ctxImg_to_img_dtc
    (folds : FoldCtx) (refs : RefList) :
    ∀ (cU cF : SmtDatatypeCons),
      (∀ q D, (q, D) ∈ folds → sizeOf cU < sizeOf (SmtType.Datatype q D)) →
      CtxImgDtc folds refs cF cU → imgDtc refs cF cU
  | SmtDatatypeCons.unit, cF, _hAbove, hImg => hImg
  | SmtDatatypeCons.cons T c, cF, hAbove, hImg => by
      rcases hImg with ⟨TF, cF', hEq, hT, hc⟩
      exact ⟨TF, cF', hEq,
        ctxImg_to_img_ty folds refs T TF
          (by
            intro q D hMem
            have hlt := hAbove q D hMem
            simp at hlt ⊢
            omega)
          hT,
        ctxImg_to_img_dtc folds refs c cF'
          (by
            intro q D hMem
            have hlt := hAbove q D hMem
            simp at hlt ⊢
            omega)
          hc⟩

private theorem ctxImg_to_img_dt
    (folds : FoldCtx) (refs : RefList) :
    ∀ (dU dF : SmtDatatype),
      (∀ q D, (q, D) ∈ folds → sizeOf dU < sizeOf (SmtType.Datatype q D)) →
      CtxImgDt folds refs dF dU → imgDt refs dF dU
  | SmtDatatype.null, dF, _hAbove, hImg => hImg
  | SmtDatatype.sum c d, dF, hAbove, hImg => by
      rcases hImg with ⟨cF, dF', hEq, hc, hd⟩
      exact ⟨cF, dF', hEq,
        ctxImg_to_img_dtc folds refs c cF
          (by
            intro q D hMem
            have hlt := hAbove q D hMem
            simp at hlt ⊢
            omega)
          hc,
        ctxImg_to_img_dt folds refs d dF'
          (by
            intro q D hMem
            have hlt := hAbove q D hMem
            simp at hlt ⊢
            omega)
          hd⟩

end

private theorem ctxImg_empty_to_img_dt
    (refs : RefList) (U F : SmtDatatype)
    (h : CtxImgDt [] refs F U) : imgDt refs F U := by
  exact ctxImg_to_img_dt [] refs U F (by simp) h

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

/-- `FoldObsTy.dt` is most conveniently established at the default-path
level.  The `refDef` equivalence above converts that syntactic implication
back to the inhabitance implication consumed by wf transport. -/
private theorem foldObsTy_dt_of_refDef
    {sOld sNew sU : native_String} {dOld dNew dU : SmtDatatype}
    (hDef : refDefDt native_reflist_nil dOld = true →
      refDefDt native_reflist_nil dNew = true)
    (hBody : FoldObsDt (__smtx_dt_substitute sOld dOld dOld)
      (__smtx_dt_substitute sNew dNew dNew) dU) :
    FoldObsTy (SmtType.Datatype sOld dOld)
      (SmtType.Datatype sNew dNew) (SmtType.Datatype sU dU) := by
  exact FoldObsTy.dt
    (fun hInh => inhabited_of_refDef_empty sNew dNew
      (hDef (refDef_empty_of_inhabited sOld dOld hInh)))
    hBody

/-- Positional substitution images of an inhabited datatype body are
inhabited.  Unlike `inhabited_chain_image`, this statement does not require a
particular list of substitutions: the origin image itself is the certificate
that rules out the arbitrary-payload counterexample. -/
private theorem inhabited_of_img
    (refs : RefList) (s : native_String) (R D : SmtDatatype)
    (hImg : imgDt refs D R)
    (hInh : native_inhabited_type (SmtType.Datatype s R) = true) :
    native_inhabited_type (SmtType.Datatype s D) = true := by
  exact inhabited_of_refDef_empty s D
    (refDef_img_dt refs R D hImg (refDef_empty_of_inhabited s R hInh))

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

/-! A raw guide reached by the structural establishment walk remains embedded
in the original root: every definition visible in the root is still respected
by the guide.  Unlike root-relative name consistency alone, this rules out a
detached guide introducing a name which the root never contained. -/
def RootEmbeddedTy (root : SmtDatatype) (T : SmtType) : Prop :=
  ∀ s X, __smtx_dt_name_agrees s X root = true →
    __smtx_type_name_agrees s X T = true

def RootEmbeddedDtc (root : SmtDatatype)
    (c : SmtDatatypeCons) : Prop :=
  ∀ s X, __smtx_dt_name_agrees s X root = true →
    __smtx_dt_cons_name_agrees s X c = true

def RootEmbeddedDt (root : SmtDatatype) (d : SmtDatatype) : Prop :=
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

private def ChainDistinct : SubstChain → Prop
  | [] => True
  | (s, _R, _P) :: REST =>
      chainHasName s REST = false ∧ ChainDistinct REST

private def rawFolds : SubstChain → FoldCtx
  | [] => []
  | (s, R, _P) :: REST => (s, R) :: rawFolds REST

/-! Payload provenance.  For an entry `(s,R,P)`, the payload is a scoped image
of `R`; later raw entries are precisely the folds still waiting to be resolved,
earlier entry names are the references already resolved, and `ambient` records
enclosing datatype binders crossed by `chain_descend`. -/
private def ChainOriginAcc (ambient : FoldCtx) (refs : RefList) :
    SubstChain → Prop
  | [] => True
  | (s, R, P) :: REST =>
      CtxImgDt (rawFolds REST ++ ambient) refs P R ∧
        ChainOriginAcc ambient (native_reflist_insert refs s) REST

/-- Every raw binder recorded in a suffix is an occurrence consistent with
the fixed raw root. -/
private def RawSuffixCons (root : SmtDatatype) : SubstChain → Prop
  | [] => True
  | (s, X, _P) :: REST =>
      __smtx_type_names_consistent_rec root (SmtType.Datatype s X) = true ∧
        RawSuffixCons root REST

/-! The corresponding occurrence invariant.  Name consistency says that a
recorded body agrees with the root; embedding additionally says it really is
part of the same definition universe, which is what makes future folds safe. -/
private def RawSuffixEmbedded (root : SmtDatatype) : SubstChain → Prop
  | [] => True
  | (s, X, _P) :: REST =>
      RootEmbeddedTy root (SmtType.Datatype s X) ∧
        RawSuffixEmbedded root REST

private def ChainRawNoStray (q : native_String) (X : SmtDatatype) :
    SubstChain → Prop
  | [] => True
  | (_s, R, _P) :: REST =>
      noStrayDt q X R = true ∧ ChainRawNoStray q X REST

private theorem chainHasName_false_parts
    (q s : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (h : chainHasName q ((s, R, P) :: REST) = false) :
    native_streq q s = false ∧ chainHasName q REST = false := by
  simpa [chainHasName, native_or, Bool.or_eq_false_iff] using h

private theorem chainHasName_append_one
    (r : native_String) (REST : SubstChain)
    (q : native_String) (X P : SmtDatatype) :
    chainHasName r (REST ++ [(q, X, P)]) =
      native_or (chainHasName r REST) (native_streq r q) := by
  induction REST with
  | nil => simp [chainHasName, native_or]
  | cons e REST ih =>
      rcases e with ⟨s, R, Q⟩
      simp [chainHasName, native_or, ih, Bool.or_assoc]

private theorem chainHasName_descend_of_fresh
    (r q : native_String) :
    ∀ (REST : SubstChain) (Y : SmtDatatype),
      chainHasName q REST = false →
      chainHasName r (chain_descend REST q Y) = chainHasName r REST
  | [], Y, _ => rfl
  | (s, R, P) :: REST, Y, hFresh => by
      have hp := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hp.1
      simp [chain_descend, hsq, chainHasName,
        chainHasName_descend_of_fresh r q REST
          (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y) hp.2]

private theorem ChainDistinct_descend_append
    (q : native_String) (X B : SmtDatatype) :
    ∀ (REST : SubstChain) (Y : SmtDatatype),
      chainHasName q REST = false → ChainDistinct REST →
      ChainDistinct (chain_descend REST q Y ++ [(q, X, B)])
  | [], Y, _hFresh, _hDistinct => ⟨rfl, trivial⟩
  | (s, R, P) :: REST, Y, hFresh, hDistinct => by
      have hFreshParts := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hFreshParts.1
      rcases hDistinct with ⟨hHead, hTail⟩
      simp only [chain_descend, hsq, if_false, List.cons_append, ChainDistinct]
      constructor
      · calc
          chainHasName s
              (List.append
                (chain_descend REST q
                  (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y))
                [(q, X, B)]) =
              native_or
                (chainHasName s
                  (chain_descend REST q
                    (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)))
                (native_streq s q) := chainHasName_append_one _ _ _ _ _
          _ = native_or (chainHasName s REST) (native_streq s q) := by
            rw [chainHasName_descend_of_fresh s q REST
              (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
              hFreshParts.2]
          _ = false := by simp [native_or, hHead, hsq]
      · exact ChainDistinct_descend_append q X B REST
          (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
          hFreshParts.2 hTail

private theorem rawFolds_append_one
    (REST : SubstChain) (s : native_String) (R P : SmtDatatype) :
    rawFolds (REST ++ [(s, R, P)]) = rawFolds REST ++ [(s, R)] := by
  induction REST with
  | nil => rfl
  | cons e REST ih =>
      rcases e with ⟨q, X, Q⟩
      simp [rawFolds, ih]

private theorem rawFolds_append (A B : SubstChain) :
    rawFolds (A ++ B) = rawFolds A ++ rawFolds B := by
  induction A with
  | nil => rfl
  | cons e A ih =>
      rcases e with ⟨q, X, Q⟩
      simp [rawFolds, ih]

private theorem rawFolds_descend_of_fresh
    (q : native_String) :
    ∀ (REST : SubstChain) (Y : SmtDatatype),
      chainHasName q REST = false →
      rawFolds (chain_descend REST q Y) = rawFolds REST
  | [], Y, _ => rfl
  | (s, R, P) :: REST, Y, hFresh => by
      have hp := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hp.1
      simp [chain_descend, hsq, rawFolds,
        rawFolds_descend_of_fresh q REST
          (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y) hp.2]

private theorem chainRefsAcc_descend_of_fresh
    (q : native_String) (refs : RefList) :
    ∀ (REST : SubstChain) (Y : SmtDatatype),
      chainHasName q REST = false →
      chainRefsAcc refs (chain_descend REST q Y) = chainRefsAcc refs REST
  | [], Y, _ => rfl
  | (s, R, P) :: REST, Y, hFresh => by
      have hp := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hp.1
      simp [chain_descend, hsq, chainRefsAcc,
        chainRefsAcc_descend_of_fresh q (native_reflist_insert refs s) REST
          (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y) hp.2]

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

private theorem RawSuffixEmbedded_descend
    (root : SmtDatatype) :
    ∀ (REST : SubstChain) (q : native_String) (X : SmtDatatype),
      RawSuffixEmbedded root REST →
      RawSuffixEmbedded root (chain_descend REST q X)
  | [], q, X, _ => trivial
  | (s, R, P) :: REST, q, X, hEmb => by
      rcases hEmb with ⟨hHead, hTail⟩
      cases hsq : native_streq s q with
      | true =>
          simpa [chain_descend, hsq] using
            RawSuffixEmbedded_descend root REST q X hTail
      | false =>
          simp only [chain_descend, hsq, if_false]
          exact ⟨hHead,
            RawSuffixEmbedded_descend root REST q
              (__smtx_dt_substitute s (__smtx_dt_lift q X P) X) hTail⟩

private theorem RawSuffixEmbedded_append
    (root : SmtDatatype) (REST : SubstChain)
    (s : native_String) (X P : SmtDatatype)
    (hREST : RawSuffixEmbedded root REST)
    (hField : RootEmbeddedTy root (SmtType.Datatype s X)) :
    RawSuffixEmbedded root (REST ++ [(s, X, P)]) := by
  induction REST with
  | nil => exact ⟨hField, trivial⟩
  | cons e REST ih =>
      rcases e with ⟨s0, X0, P0⟩
      rcases hREST with ⟨hHead, hTail⟩
      exact ⟨hHead, ih hTail⟩

/-! Extending a provenance-valid chain preserves provenance.  The proof is
purely positional: every old payload is lifted, which adds the new raw node to
its fold scope, while the appended payload is an ordinary prefix-chain image
of its raw body. -/
private theorem ChainOriginAcc_descend_append
    (ambient : FoldCtx) (q : native_String) (X B : SmtDatatype)
    (hTarget : noStrayDt q X X = true) :
    ∀ (REST : SubstChain) (refs : RefList) (Y : SmtDatatype),
      chainHasName q REST = false →
      ChainRawNoStray q X REST →
      ChainOriginAcc ambient refs REST →
      CtxImgDt ambient (chainRefsAcc refs REST) B X →
      ChainOriginAcc ambient refs
        (chain_descend REST q Y ++ [(q, X, B)])
  | [], refs, Y, _hFresh, _hRaw, _hOrigin, hB => by
      exact ⟨by simpa [rawFolds] using hB, trivial⟩
  | (s, R, P) :: REST, refs, Y, hFresh, hRaw, hOrigin, hB => by
      have hFreshParts := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hFreshParts.1
      rcases hRaw with ⟨hNoR, hRawTail⟩
      rcases hOrigin with ⟨hP, hOriginTail⟩
      have hLift := ctxImg_lift_dt (rawFolds REST ++ ambient) refs
        q X Y hTarget R P hNoR hP
      have hLift' :
          CtxImgDt (rawFolds REST ++ (q, X) :: ambient) refs
            (__smtx_dt_lift q Y P) R := by
        exact ctxImg_mono_dt
          (folds := (q, X) :: (rawFolds REST ++ ambient))
          (folds' := rawFolds REST ++ (q, X) :: ambient)
          (refs := refs) (refs' := refs)
          (by
            intro p hp
            simp only [List.mem_cons, List.mem_append] at hp ⊢
            rcases hp with rfl | hp
            · exact Or.inr (Or.inl rfl)
            · rcases hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr (Or.inr hp))
          (fun _ h => h) R _ hLift
      have hTail := ChainOriginAcc_descend_append ambient q X B hTarget
        REST (native_reflist_insert refs s)
        (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
        hFreshParts.2 hRawTail hOriginTail hB
      simp only [chain_descend, hsq, if_false, List.cons_append,
        ChainOriginAcc]
      constructor
      · have hRawFolds :
            rawFolds
                (chain_descend REST q
                    (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y) ++
                  [(q, X, B)]) =
              rawFolds REST ++ [(q, X)] := by
            calc
              _ = rawFolds
                    (chain_descend REST q
                      (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)) ++
                    rawFolds [(q, X, B)] := rawFolds_append _ _
              _ = rawFolds REST ++ [(q, X)] := by
                rw [rawFolds_descend_of_fresh q REST
                  (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
                  hFreshParts.2]
                rfl
        have hScope :
            rawFolds
                  (List.append
                    (chain_descend REST q
                      (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y))
                    [(q, X, B)]) ++ ambient =
              rawFolds REST ++ (q, X) :: ambient := by
          calc
            _ = (rawFolds REST ++ [(q, X)]) ++ ambient :=
              congrArg (fun fs => fs ++ ambient) hRawFolds
            _ = rawFolds REST ++ (q, X) :: ambient := by
              simp [List.append_assoc]
        exact Eq.mp
          (congrArg
            (fun fs => CtxImgDt fs refs (__smtx_dt_lift q Y P) R)
            hScope.symm)
          hLift'
      · exact hTail

private theorem ChainOriginAcc_descend
    (ambient : FoldCtx) (q : native_String) (X : SmtDatatype)
    (hTarget : noStrayDt q X X = true) :
    ∀ (REST : SubstChain) (refs : RefList) (Y : SmtDatatype),
      chainHasName q REST = false →
      ChainRawNoStray q X REST →
      ChainOriginAcc ambient refs REST →
      ChainOriginAcc ((q, X) :: ambient) refs (chain_descend REST q Y)
  | [], refs, Y, _hFresh, _hRaw, _hOrigin => trivial
  | (s, R, P) :: REST, refs, Y, hFresh, hRaw, hOrigin => by
      have hFreshParts := chainHasName_false_parts q s R P REST hFresh
      have hsq : native_streq s q = false := by
        simpa [native_streq, eq_comm] using hFreshParts.1
      rcases hRaw with ⟨hNoR, hRawTail⟩
      rcases hOrigin with ⟨hP, hOriginTail⟩
      have hLift := ctxImg_lift_dt (rawFolds REST ++ ambient) refs
        q X Y hTarget R P hNoR hP
      have hLift' :
          CtxImgDt (rawFolds REST ++ (q, X) :: ambient) refs
            (__smtx_dt_lift q Y P) R := by
        exact ctxImg_mono_dt
          (folds := (q, X) :: (rawFolds REST ++ ambient))
          (folds' := rawFolds REST ++ (q, X) :: ambient)
          (refs := refs) (refs' := refs)
          (by
            intro p hp
            simp only [List.mem_cons, List.mem_append] at hp ⊢
            rcases hp with rfl | hp
            · exact Or.inr (Or.inl rfl)
            · rcases hp with hp | hp
              · exact Or.inl hp
              · exact Or.inr (Or.inr hp))
          (fun _ h => h) R _ hLift
      have hTail := ChainOriginAcc_descend ambient q X hTarget
        REST (native_reflist_insert refs s)
        (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
        hFreshParts.2 hRawTail hOriginTail
      simp only [chain_descend, hsq, if_false, ChainOriginAcc]
      constructor
      · have hRF := rawFolds_descend_of_fresh q REST
            (__smtx_dt_substitute s (__smtx_dt_lift q Y P) Y)
            hFreshParts.2
        exact Eq.mp
          (congrArg
            (fun fs => CtxImgDt (fs ++ (q, X) :: ambient) refs
              (__smtx_dt_lift q Y P) R)
            hRF.symm)
          hLift'
      · exact hTail

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

private theorem ChainRawNoStray_of_embedded
    (root : SmtDatatype) (q : native_String) (X : SmtDatatype)
    (hAt : __smtx_dt_name_agrees q X root = true) :
    ∀ (REST : SubstChain), RawSuffixEmbedded root REST →
      ChainRawNoStray q X REST
  | [], _ => trivial
  | (s, R, P) :: REST, hEmb => by
      rcases hEmb with ⟨hHead, hTail⟩
      have hBody := RootEmbeddedTy_body root s R hHead
      exact ⟨noStrayDt_of_name_agrees q X R (hBody q X hAt),
        ChainRawNoStray_of_embedded root q X hAt REST hTail⟩

private def ChainSourceOK (t : native_String) (R P : SmtDatatype)
    (REST : SubstChain) : Prop :=
  P = liftSources REST R ∧
    __smtx_type_names_consistent (SmtType.Datatype t R) = true ∧
      native_inhabited_type (SmtType.Datatype t R) = true ∧
        RawSuffixCons R REST ∧
          RawSuffixEmbedded R REST ∧
            ChainOriginAcc [] native_reflist_nil ((t, R, P) :: REST) ∧
              ChainDistinct ((t, R, P) :: REST)

private theorem ChainSourceOK_descend
    (t q : native_String) (R P X Y : SmtDatatype)
    (REST : SubstChain)
    (hSource : ChainSourceOK t R P REST)
    (hne : native_streq t q = false)
    (hFresh : chainHasName q REST = false)
    (hField : __smtx_type_names_consistent_rec R
      (SmtType.Datatype q X) = true)
    (hEmbed : RootEmbeddedTy R (SmtType.Datatype q X)) :
    ChainSourceOK t R (__smtx_dt_lift q X P)
      (chain_descend REST q Y ++
        [(q, X, chain_dt (chain_descend ((t, R, P) :: REST) q X) X)]) := by
  rcases hSource with
    ⟨hPayload, hRoot, hRootInh, hREST, hRESTEmb, hOrigin, hDistinct⟩
  let B := chain_dt (chain_descend ((t, R, P) :: REST) q X) X
  let NEWREST := chain_descend REST q Y ++ [(q, X, B)]
  have hFieldParts := namesConsTy_parts R q X hField
  have hTarget : noStrayDt q X X = true :=
    noStrayDt_of_name_agrees q X X
      ((RootEmbeddedTy_body R q X hEmbed) q X hFieldParts.1)
  have hHeadNo : noStrayDt q X R = true :=
    noStrayDt_of_name_agrees q X R hFieldParts.1
  have hTailRaw : ChainRawNoStray q X REST :=
    ChainRawNoStray_of_embedded R q X hFieldParts.1 REST hRESTEmb
  have hqt : native_streq q t = false := by
    simpa [native_streq, eq_comm] using hne
  have hFreshAll : chainHasName q ((t, R, P) :: REST) = false := by
    simp [chainHasName, native_or, hqt, hFresh]
  have hBImg : imgDt
      (chainRefsAcc (native_reflist_insert native_reflist_nil t) REST) B X := by
    have hImg := chain_dt_img (chain_descend ((t, R, P) :: REST) q X) X
    rw [chainRefs, chainRefsAcc_descend_of_fresh q native_reflist_nil
      ((t, R, P) :: REST) X hFreshAll] at hImg
    simpa [chainRefsAcc, B] using hImg
  rcases hOrigin with ⟨hHeadOrigin, hTailOrigin⟩
  have hTailOrigin' : ChainOriginAcc []
      (native_reflist_insert native_reflist_nil t) NEWREST := by
    exact ChainOriginAcc_descend_append [] q X B hTarget REST
      (native_reflist_insert native_reflist_nil t) Y hFresh hTailRaw
      hTailOrigin (ctxImg_of_img_dt [] _ X B hBImg)
  have hHeadOrigin0 : CtxImgDt (rawFolds REST) native_reflist_nil P R := by
    simpa using hHeadOrigin
  have hHeadLift := ctxImg_lift_dt (rawFolds REST) native_reflist_nil
    q X X hTarget R P hHeadNo hHeadOrigin0
  have hHeadOrigin' : CtxImgDt (rawFolds NEWREST) native_reflist_nil
      (__smtx_dt_lift q X P) R := by
    apply ctxImg_mono_dt
      (folds := (q, X) :: rawFolds REST)
      (folds' := rawFolds NEWREST)
      (refs := native_reflist_nil) (refs' := native_reflist_nil)
      _ (fun _ h => h) R _ hHeadLift
    intro p hp
    simp only [NEWREST, rawFolds_append_one,
      rawFolds_descend_of_fresh q REST Y hFresh, List.mem_cons,
      List.mem_append] at hp ⊢
    rcases hp with rfl | hp
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hp
  rcases hDistinct with ⟨hHeadDistinct, hTailDistinct⟩
  have hTailDistinct' : ChainDistinct NEWREST :=
    ChainDistinct_descend_append q X B REST Y hFresh hTailDistinct
  have hHeadDistinct' : chainHasName t NEWREST = false := by
    rw [chainHasName_append_one,
      chainHasName_descend_of_fresh t q REST Y hFresh]
    simp [native_or, hHeadDistinct, hne]
  refine ⟨?_, hRoot, hRootInh, ?_, ?_, ?_, ?_⟩
  · rw [liftSources_append_one,
      liftSources_descend_of_fresh q REST Y R hFresh, ← hPayload]
  · exact RawSuffixCons_append R (chain_descend REST q Y) q X B
      (RawSuffixCons_descend R REST q Y hREST) hField
  · exact RawSuffixEmbedded_append R (chain_descend REST q Y) q X B
      (RawSuffixEmbedded_descend R REST q Y hRESTEmb) hEmbed
  · exact ⟨by simpa [NEWREST] using hHeadOrigin', hTailOrigin'⟩
  · exact ⟨by simpa [NEWREST] using hHeadDistinct', hTailDistinct'⟩

private theorem type_name_agrees_same_body
    (s : native_String) (A D : SmtDatatype)
    (h : __smtx_type_name_agrees s A (SmtType.Datatype s D) = true) :
    A = D := by
  have hp : A = D ∧ __smtx_dt_name_agrees s A D = true := by
    simpa [__smtx_type_name_agrees, native_streq, native_Teq, native_ite]
      using h
  exact hp.1

/-! Resolve one pending fold.  The entry payload is an image of its recorded
raw body.  Root consistency and embedding identify every same-named raw node,
including beneath another datatype binder where the payload is lifted again. -/
mutual

private theorem ctxImg_resolve_ty
    (root : SmtDatatype) (s : native_String) (R P : SmtDatatype)
    (folds : FoldCtx) (refs : RefList)
    (hEntryEmb : RootEmbeddedTy root (SmtType.Datatype s R))
    (hP : CtxImgDt folds refs P R) :
    ∀ (U F : SmtType),
      __smtx_type_names_consistent_rec root U = true →
      RootEmbeddedTy root U →
      CtxImgTy ((s, R) :: folds) refs F U →
      CtxImgTy folds (native_reflist_insert refs s)
        (__smtx_type_substitute s P F) U
  | SmtType.TypeRef q, F, _hCons, _hEmb, hImg => by
      rcases hImg with rfl | ⟨hq, D, rfl⟩
      · cases hsq : native_streq s q with
        | true =>
            have heq : s = q := by simpa [native_streq] using hsq
            subst q
            exact Or.inr ⟨by
              simp [native_reflist_contains, native_reflist_insert], P, by
              simp [__smtx_type_substitute, native_ite, native_streq]⟩
        | false =>
            exact Or.inl (by simp [__smtx_type_substitute, native_ite, hsq])
      · exact Or.inr ⟨by
            simp only [native_reflist_contains, native_reflist_insert,
              List.mem_cons, decide_eq_true_eq]
            exact Or.inr (by simpa [native_reflist_contains] using hq),
          _, rfl⟩
  | SmtType.Datatype q D, F, hCons, hEmb, hImg => by
      have hConsParts := namesConsTy_parts root q D hCons
      have hEmbBody := RootEmbeddedTy_body root q D hEmb
      have hEntryBody := RootEmbeddedTy_body root s R hEntryEmb
      have hNoD : noStrayDt q D D = true :=
        noStrayDt_of_name_agrees q D D (hEmbBody q D hConsParts.1)
      have hNoR : noStrayDt q D R = true :=
        noStrayDt_of_name_agrees q D R (hEntryBody q D hConsParts.1)
      rcases hImg with ⟨hMem, rfl⟩ | ⟨DF, rfl, hBody⟩
      · cases hsq : native_streq s q with
        | true =>
            have heq : s = q := by simpa [native_streq] using hsq
            subst q
            have hDR : D = R :=
              type_name_agrees_same_body s D R (hEntryEmb s D hConsParts.1)
            subst D
            refine Or.inr ⟨P, by
              simp [__smtx_type_substitute, native_ite, native_streq], ?_⟩
            exact ctxImg_mono_dt
              (folds := folds) (folds' := (s, R) :: folds)
              (refs := refs) (refs' := native_reflist_insert refs s)
              (by
                intro p hp
                simp only [List.mem_cons]
                exact Or.inr hp)
              (by
                intro r hr
                simp only [native_reflist_contains, native_reflist_insert,
                  List.mem_cons, decide_eq_true_eq]
                exact Or.inr (by simpa [native_reflist_contains] using hr))
              R P hP
        | false =>
            refine Or.inl ⟨?_, by
              simp [__smtx_type_substitute, native_ite, hsq]⟩
            simp only [List.mem_cons] at hMem
            rcases hMem with hEq | hMem
            · have hName : q = s := congrArg Prod.fst hEq
              subst q
              simp [native_streq] at hsq
            · exact hMem
      · cases hsq : native_streq s q with
        | true =>
            have heq : s = q := by simpa [native_streq] using hsq
            subst q
            have hDR : D = R :=
              type_name_agrees_same_body s D R (hEntryEmb s D hConsParts.1)
            subst D
            refine Or.inr ⟨DF, by
              simp [__smtx_type_substitute, native_ite, native_streq], ?_⟩
            exact ctxImg_mono_dt
              (folds := (s, R) :: (s, R) :: folds)
              (folds' := (s, R) :: folds)
              (refs := refs) (refs' := native_reflist_insert refs s)
              (by
                intro p hp
                simp only [List.mem_cons] at hp ⊢
                rcases hp with rfl | rfl | hp
                · exact Or.inl rfl
                · exact Or.inl rfl
                · exact Or.inr hp)
              (by
                intro r hr
                simp only [native_reflist_contains, native_reflist_insert,
                  List.mem_cons, decide_eq_true_eq]
                exact Or.inr (by simpa [native_reflist_contains] using hr))
              R DF hBody
        | false =>
            refine Or.inr ⟨__smtx_dt_substitute s (__smtx_dt_lift q DF P) DF,
              by simp [__smtx_type_substitute, native_ite, hsq], ?_⟩
            have hPayload := ctxImg_lift_dt folds refs q D DF hNoD R P hNoR hP
            have hBody' : CtxImgDt ((s, R) :: (q, D) :: folds) refs DF D := by
              exact ctxImg_mono_dt
                (folds := (q, D) :: (s, R) :: folds)
                (folds' := (s, R) :: (q, D) :: folds)
                (refs := refs) (refs' := refs)
                (by
                  intro p hp
                  simp only [List.mem_cons] at hp ⊢
                  rcases hp with rfl | rfl | hp
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr hp))
                (fun _ h => h) D DF hBody
            exact ctxImg_resolve_dt root s R (__smtx_dt_lift q DF P)
              ((q, D) :: folds) refs hEntryEmb hPayload D DF
              hConsParts.2 hEmbBody hBody'
  | SmtType.None, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Bool, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Int, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Real, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.RegLan, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.BitVec w, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Map A B, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Set A, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Seq A, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.Char, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.USort u, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.FunType A B, F, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtType.DtcAppType A B, F, _hCons, _hEmb, hImg => by cases hImg; rfl

private theorem ctxImg_resolve_dtc
    (root : SmtDatatype) (s : native_String) (R P : SmtDatatype)
    (folds : FoldCtx) (refs : RefList)
    (hEntryEmb : RootEmbeddedTy root (SmtType.Datatype s R))
    (hP : CtxImgDt folds refs P R) :
    ∀ (cU cF : SmtDatatypeCons),
      __smtx_dt_cons_names_consistent_rec root cU = true →
      RootEmbeddedDtc root cU →
      CtxImgDtc ((s, R) :: folds) refs cF cU →
      CtxImgDtc folds (native_reflist_insert refs s)
        (__smtx_dtc_substitute s P cF) cU
  | SmtDatatypeCons.unit, cF, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtDatatypeCons.cons T c, cF, hCons, hEmb, hImg => by
      rcases hImg with ⟨TF, cF', rfl, hT, hc⟩
      have hConsParts := namesConsDtc_parts root T c hCons
      have hEmbParts := RootEmbeddedDtc_parts root T c hEmb
      exact ⟨_, _, rfl,
        ctxImg_resolve_ty root s R P folds refs hEntryEmb hP T TF
          hConsParts.1 hEmbParts.1 hT,
        ctxImg_resolve_dtc root s R P folds refs hEntryEmb hP c cF'
          hConsParts.2 hEmbParts.2 hc⟩

private theorem ctxImg_resolve_dt
    (root : SmtDatatype) (s : native_String) (R P : SmtDatatype)
    (folds : FoldCtx) (refs : RefList)
    (hEntryEmb : RootEmbeddedTy root (SmtType.Datatype s R))
    (hP : CtxImgDt folds refs P R) :
    ∀ (dU dF : SmtDatatype),
      __smtx_dt_names_consistent_rec root dU = true →
      RootEmbeddedDt root dU →
      CtxImgDt ((s, R) :: folds) refs dF dU →
      CtxImgDt folds (native_reflist_insert refs s)
        (__smtx_dt_substitute s P dF) dU
  | SmtDatatype.null, dF, _hCons, _hEmb, hImg => by cases hImg; rfl
  | SmtDatatype.sum c d, dF, hCons, hEmb, hImg => by
      rcases hImg with ⟨cF, dF', rfl, hc, hd⟩
      have hConsParts := namesConsDt_parts root c d hCons
      have hEmbParts := RootEmbeddedDt_parts root c d hEmb
      exact ⟨_, _, rfl,
        ctxImg_resolve_dtc root s R P folds refs hEntryEmb hP c cF
          hConsParts.1 hEmbParts.1 hc,
        ctxImg_resolve_dt root s R P folds refs hEntryEmb hP d dF'
          hConsParts.2 hEmbParts.2 hd⟩

end

private theorem ctxImg_resolve_chain
    (root : SmtDatatype) (ambient : FoldCtx) :
    ∀ (REST : SubstChain) (refs : RefList) (U F : SmtDatatype),
      RawSuffixEmbedded root REST →
      ChainOriginAcc ambient refs REST →
      __smtx_dt_names_consistent_rec root U = true →
      RootEmbeddedDt root U →
      CtxImgDt (rawFolds REST ++ ambient) refs F U →
      CtxImgDt ambient (chainRefsAcc refs REST) (chain_dt REST F) U
  | [], refs, U, F, _hRESTEmb, _hOrigin, _hCons, _hEmb, hImg => by
      simpa [rawFolds, chainRefsAcc, chain_dt] using hImg
  | (s, R, P) :: REST, refs, U, F, hRESTEmb, hOrigin, hCons, hEmb,
      hImg => by
      rcases hRESTEmb with ⟨hEntryEmb, hTailEmb⟩
      rcases hOrigin with ⟨hP, hTailOrigin⟩
      have hImg0 : CtxImgDt ((s, R) :: (rawFolds REST ++ ambient)) refs F U := by
        simpa [rawFolds] using hImg
      have hStep := ctxImg_resolve_dt root s R P
        (rawFolds REST ++ ambient) refs hEntryEmb hP U F hCons hEmb hImg0
      have hRec := ctxImg_resolve_chain root ambient REST
        (native_reflist_insert refs s) U (__smtx_dt_substitute s P F)
        hTailEmb hTailOrigin hCons hEmb hStep
      simpa [chain_dt, chainRefsAcc] using hRec

private theorem type_names_consistent_parts
    (t : native_String) (R : SmtDatatype)
    (h : __smtx_type_names_consistent (SmtType.Datatype t R) = true) :
    __smtx_dt_name_agrees t R R = true ∧
      __smtx_dt_names_consistent_rec R R = true := by
  simp only [__smtx_type_names_consistent] at h
  cases ha : __smtx_dt_name_agrees t R R <;>
    cases hc : __smtx_dt_names_consistent_rec R R <;>
      simp_all [native_ite]

/-! The canonical resolution of a provenance-valid head is a positional image
of its raw root.  The only fold left after resolving the suffix is the outer
`Datatype t R` binder itself, which cannot occur inside `R` by strict size. -/
private theorem chainSource_head_img
    (t : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (hSource : ChainSourceOK t R P REST) :
    imgDt
      (chainRefsAcc (native_reflist_insert native_reflist_nil t)
        (chain_descend REST t P))
      (chain_dt (chain_descend REST t P) P) R := by
  rcases hSource with
    ⟨_hPayload, hRoot, _hRootInh, _hRESTCons, hRESTEmb, hOrigin,
      hDistinct⟩
  rcases hOrigin with ⟨hP, hTailOrigin⟩
  rcases hDistinct with ⟨hFresh, _hTailDistinct⟩
  have hRootParts := type_names_consistent_parts t R hRoot
  have hTarget : noStrayDt t R R = true :=
    noStrayDt_of_name_agrees t R R hRootParts.1
  have hRaw : ChainRawNoStray t R REST :=
    ChainRawNoStray_of_embedded R t R hRootParts.1 REST hRESTEmb
  have hDescOrigin : ChainOriginAcc [(t, R)]
      (native_reflist_insert native_reflist_nil t)
      (chain_descend REST t P) := by
    exact ChainOriginAcc_descend [] t R hTarget REST
      (native_reflist_insert native_reflist_nil t) P hFresh hRaw hTailOrigin
  have hP0 : CtxImgDt (rawFolds REST) native_reflist_nil P R := by
    simpa using hP
  have hPStart :
      CtxImgDt (rawFolds (chain_descend REST t P) ++ [(t, R)])
        (native_reflist_insert native_reflist_nil t) P R := by
    apply ctxImg_mono_dt
      (folds := rawFolds REST)
      (folds' := rawFolds (chain_descend REST t P) ++ [(t, R)])
      (refs := native_reflist_nil)
      (refs' := native_reflist_insert native_reflist_nil t)
      _ _ R P hP0
    · intro p hp
      rw [rawFolds_descend_of_fresh t REST P hFresh]
      exact List.mem_append_left _ hp
    · intro q hq
      simp [native_reflist_contains, native_reflist_nil] at hq
  have hResolved := ctxImg_resolve_chain R [(t, R)]
    (chain_descend REST t P) (native_reflist_insert native_reflist_nil t)
    R P (RawSuffixEmbedded_descend R REST t P hRESTEmb) hDescOrigin
    hRootParts.2 (fun _ _ hAt => hAt) hPStart
  exact ctxImg_to_img_dt [(t, R)] _ R
    (chain_dt (chain_descend REST t P) P)
    (by
      intro q D hMem
      simp only [List.mem_singleton] at hMem
      cases hMem
      simp
      omega)
    hResolved

/-! A structure no larger than the body being folded cannot contain the full
`Datatype s X` node, whose size is strictly larger than `X`.  These lemmas
turn a nontrivial lift into the strict-size fact needed to show that every
enclosing binder is absent from the folded body's raw source. -/
mutual

private theorem lift_eq_of_size_le_ty (s : native_String) (X : SmtDatatype) :
    ∀ T : SmtType, sizeOf T ≤ sizeOf X → __smtx_type_lift s X T = T
  | SmtType.Datatype q D, hSize => by
      by_cases hEq : native_Teq
          (SmtType.Datatype s X) (SmtType.Datatype q D) = true
      · have hp : s = q ∧ X = D := by simpa [native_Teq] using hEq
        rw [← hp.2] at hSize
        simp at hSize
        omega
      · simp [__smtx_type_lift, native_ite, hEq,
          lift_eq_of_size_le_dt s X D (by simp at hSize ⊢; omega)]
  | SmtType.None, _ => by simp [__smtx_type_lift]
  | SmtType.Bool, _ => by simp [__smtx_type_lift]
  | SmtType.Int, _ => by simp [__smtx_type_lift]
  | SmtType.Real, _ => by simp [__smtx_type_lift]
  | SmtType.RegLan, _ => by simp [__smtx_type_lift]
  | SmtType.BitVec w, _ => by simp [__smtx_type_lift]
  | SmtType.Map A B, _ => by simp [__smtx_type_lift]
  | SmtType.Set A, _ => by simp [__smtx_type_lift]
  | SmtType.Seq A, _ => by simp [__smtx_type_lift]
  | SmtType.Char, _ => by simp [__smtx_type_lift]
  | SmtType.TypeRef r, _ => by simp [__smtx_type_lift]
  | SmtType.USort u, _ => by simp [__smtx_type_lift]
  | SmtType.FunType A B, _ => by simp [__smtx_type_lift]
  | SmtType.DtcAppType A B, _ => by simp [__smtx_type_lift]

private theorem lift_eq_of_size_le_dtc (s : native_String) (X : SmtDatatype) :
    ∀ c : SmtDatatypeCons, sizeOf c ≤ sizeOf X → __smtx_dtc_lift s X c = c
  | SmtDatatypeCons.unit, _ => by simp [__smtx_dtc_lift]
  | SmtDatatypeCons.cons T c, hSize => by
      simp [__smtx_dtc_lift,
        lift_eq_of_size_le_ty s X T (by simp at hSize ⊢; omega),
        lift_eq_of_size_le_dtc s X c (by simp at hSize ⊢; omega)]

private theorem lift_eq_of_size_le_dt (s : native_String) (X : SmtDatatype) :
    ∀ D : SmtDatatype, sizeOf D ≤ sizeOf X → __smtx_dt_lift s X D = D
  | SmtDatatype.null, _ => by simp [__smtx_dt_lift]
  | SmtDatatype.sum c D, hSize => by
      simp [__smtx_dt_lift,
        lift_eq_of_size_le_dtc s X c (by simp at hSize ⊢; omega),
        lift_eq_of_size_le_dt s X D (by simp at hSize ⊢; omega)]

end

private theorem size_lt_of_lift_ne
    (s : native_String) (X D : SmtDatatype)
    (hNe : __smtx_dt_lift s X D ≠ D) :
    sizeOf X < sizeOf D := by
  apply Nat.lt_of_not_ge
  intro h
  exact hNe (lift_eq_of_size_le_dt s X D h)

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

/- The non-stable descent case, restricted to a subtree that actually uses
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

/-! ## Rotation transport

The unstable branch is discharged through a *rotation certificate*: outside
`s3`-named datatype nodes the old and new resolutions are positionally equal,
and each paired `s3` node carries the inhabitedness implication between its
two bodies.  Machine sweeps over every establishment-walk descent event
reachable from small well-formed roots (≈2000 events, 63 with an unstable
resolution) confirm both the shape claim and the per-spot implications, at
the top pair and at every diagonal re-rooting along the new payload guide.

`RotTy/RotDtc/RotDt` is the positional relation used *inside* rotated
regions and at constructor fields: identical everywhere except that a
same-named datatype pair may differ (constructor `dt`), and an `s3`-named
pair may have arbitrary bodies provided the inhabitedness implication holds
(constructor `rot`).  Since an empty-excuse default path never visits a
reference and stops only at defaultable atoms, such a path on the old side
replays on the new side, grafting a fresh sub-path at each `s3` spot from
the carried implication (`rotDt_refDef`).

`RotAllTy/RotAllDtc/RotAllDt` is the guide-indexed certificate consumed by
the wf transport: it mirrors the `FoldObs` walk, carrying at every
guide-datatype node the `Rot` relation of the two folded bodies (for the
inhabitedness implication) and, recursively, the certificate for the two
diagonal re-rootings against the guide body.  Because the guide strictly
shrinks at the recursion, certificates are finite even though the related
sides grow under self-substitution. -/

mutual

private inductive RotTy (s3 : native_String) : SmtType → SmtType → Prop where
  | same (T : SmtType) : RotTy s3 T T
  | dt {q : native_String} {ZO ZN : SmtDatatype} :
      RotDt s3 ZO ZN →
      RotTy s3 (SmtType.Datatype q ZO) (SmtType.Datatype q ZN)
  | rot {ZO ZN : SmtDatatype} :
      (native_inhabited_type (SmtType.Datatype s3 ZO) = true →
        native_inhabited_type (SmtType.Datatype s3 ZN) = true) →
      RotTy s3 (SmtType.Datatype s3 ZO) (SmtType.Datatype s3 ZN)
  /-- an old-side reference admits any new side: an empty-excuse default
  path never visits a reference, so transport is vacuous there.  This
  absorbs the one-sided fold flips created by descending lifts (the old
  history folds an occurrence that the new history's lift target no longer
  matches, or vice versa with the roles of the two histories exchanged at
  the head binder). -/
  | refFlip {r : native_String} {TN : SmtType} :
      RotTy s3 (SmtType.TypeRef r) TN

private inductive RotDtc (s3 : native_String) :
    SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : RotDtc s3 SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TO TN : SmtType} {cO cN : SmtDatatypeCons} :
      RotTy s3 TO TN → RotDtc s3 cO cN →
      RotDtc s3 (SmtDatatypeCons.cons TO cO) (SmtDatatypeCons.cons TN cN)

private inductive RotDt (s3 : native_String) :
    SmtDatatype → SmtDatatype → Prop where
  | null : RotDt s3 SmtDatatype.null SmtDatatype.null
  | sum {cO cN : SmtDatatypeCons} {dO dN : SmtDatatype} :
      RotDtc s3 cO cN → RotDt s3 dO dN →
      RotDt s3 (SmtDatatype.sum cO dO) (SmtDatatype.sum cN dN)

end

mutual

private theorem rotTy_defPath {s3 : native_String} :
    ∀ {TO TN : SmtType}, RotTy s3 TO TN →
      DefPathTy native_reflist_nil TO →
      DefPathTy native_reflist_nil TN := by
  intro TO TN hRot hPath
  cases hRot with
  | same _ => exact hPath
  | dt hBody =>
      cases hPath with
      | dt hP => exact DefPathTy.dt (rotDt_defPath hBody hP)
      | atom _ hDt _ => exact absurd rfl (hDt _ _)
  | rot hInh =>
      cases hPath with
      | dt hP =>
          exact DefPathTy.dt (defPathDt_of_refDef _ _
            (refDef_empty_of_inhabited s3 _
              (hInh (inhabited_of_refDef_empty s3 _
                (refDef_of_defPathDt hP)))))
      | atom _ hDt _ => exact absurd rfl (hDt _ _)
  | refFlip =>
      cases hPath with
      | ref h =>
          simp [native_reflist_contains, native_reflist_nil] at h
      | atom hRef _ _ => exact absurd rfl (hRef _)

private theorem rotDtc_defPath {s3 : native_String} :
    ∀ {cO cN : SmtDatatypeCons}, RotDtc s3 cO cN →
      DefPathDtc native_reflist_nil cO →
      DefPathDtc native_reflist_nil cN := by
  intro cO cN hRot hPath
  cases hRot with
  | unit => exact hPath
  | cons hT hc =>
      cases hPath with
      | cons hPT hPc =>
          exact DefPathDtc.cons (rotTy_defPath hT hPT)
            (rotDtc_defPath hc hPc)

private theorem rotDt_defPath {s3 : native_String} :
    ∀ {dO dN : SmtDatatype}, RotDt s3 dO dN →
      DefPathDt native_reflist_nil dO →
      DefPathDt native_reflist_nil dN := by
  intro dO dN hRot hPath
  cases hRot with
  | null => exact hPath
  | sum hc hd =>
      cases hPath with
      | head hPc => exact DefPathDt.head (rotDtc_defPath hc hPc)
      | tail hPd => exact DefPathDt.tail (rotDt_defPath hd hPd)

end

/-- Empty-excuse defaultability transports along the rotation relation. -/
private theorem rotDt_refDef {s3 : native_String} {dO dN : SmtDatatype}
    (hRot : RotDt s3 dO dN)
    (hDef : refDefDt native_reflist_nil dO = true) :
    refDefDt native_reflist_nil dN = true :=
  refDef_of_defPathDt
    (rotDt_defPath hRot (defPathDt_of_refDef native_reflist_nil dO hDef))

mutual

private inductive RotAllTy (s3 : native_String) :
    SmtType → SmtType → SmtType → Prop where
  /-- equal folded sides are transparent to the wf walk at any guide. -/
  | same (U T : SmtType) : RotAllTy s3 U T T
  /-- reference guide over a non-datatype old side: the walk skips or fails
  identically regardless of the new side. -/
  | refOld {r : native_String} {TO TN : SmtType}
      (hOld : ∀ (q : native_String) (D : SmtDatatype),
        TO ≠ SmtType.Datatype q D) :
      RotAllTy s3 (SmtType.TypeRef r) TO TN
  /-- reference guide over two datatype-shaped sides: pattern-1 skip. -/
  | refDt {r sO sN : native_String} {ZO ZN : SmtDatatype} :
      RotAllTy s3 (SmtType.TypeRef r) (SmtType.Datatype sO ZO)
        (SmtType.Datatype sN ZN)
  /-- datatype guide: the bodies are rotation-related (supplying the
  inhabitedness implication), and the two diagonal re-rootings are
  certified against the guide body. -/
  | dt {sU q : native_String} {dU ZO ZN : SmtDatatype} :
      RotDt s3 ZO ZN →
      RotAllDt s3 dU (__smtx_dt_substitute q ZO ZO)
        (__smtx_dt_substitute q ZN ZN) →
      RotAllTy s3 (SmtType.Datatype sU dU) (SmtType.Datatype q ZO)
        (SmtType.Datatype q ZN)

private inductive RotAllDtc (s3 : native_String) :
    SmtDatatypeCons → SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : RotAllDtc s3 SmtDatatypeCons.unit SmtDatatypeCons.unit
      SmtDatatypeCons.unit
  | cons {TU TO TN : SmtType} {cU cO cN : SmtDatatypeCons} :
      RotAllTy s3 TU TO TN → RotAllDtc s3 cU cO cN →
      RotAllDtc s3 (SmtDatatypeCons.cons TU cU)
        (SmtDatatypeCons.cons TO cO) (SmtDatatypeCons.cons TN cN)

private inductive RotAllDt (s3 : native_String) :
    SmtDatatype → SmtDatatype → SmtDatatype → Prop where
  | null : RotAllDt s3 SmtDatatype.null SmtDatatype.null SmtDatatype.null
  | sum {cU cO cN : SmtDatatypeCons} {dU dO dN : SmtDatatype} :
      RotAllDtc s3 cU cO cN → RotAllDt s3 dU dO dN →
      RotAllDt s3 (SmtDatatype.sum cU dU) (SmtDatatype.sum cO dO)
        (SmtDatatype.sum cN dN)

end

mutual

private theorem rotAllTy_foldObs {s3 : native_String} :
    ∀ {TU TO TN : SmtType}, RotAllTy s3 TU TO TN → FoldObsTy TO TN TU
  | _, _, _, RotAllTy.same U T => FoldObsTy.same T U
  | _, _, _, RotAllTy.refOld hOld => FoldObsTy.deadRef hOld
  | _, _, _, RotAllTy.refDt => FoldObsTy.ref
  | _, _, _, RotAllTy.dt hRot hRec =>
      foldObsTy_dt_of_refDef (fun h => rotDt_refDef hRot h)
        (rotAllDt_foldObs hRec)

private theorem rotAllDtc_foldObs {s3 : native_String} :
    ∀ {cU cO cN : SmtDatatypeCons}, RotAllDtc s3 cU cO cN →
      FoldObsDtc cO cN cU
  | _, _, _, RotAllDtc.unit => FoldObsDtc.unit
  | _, _, _, RotAllDtc.cons hT hc =>
      FoldObsDtc.cons (rotAllTy_foldObs hT) (rotAllDtc_foldObs hc)

private theorem rotAllDt_foldObs {s3 : native_String} :
    ∀ {dU dO dN : SmtDatatype}, RotAllDt s3 dU dO dN → FoldObsDt dO dN dU
  | _, _, _, RotAllDt.null => FoldObsDt.null
  | _, _, _, RotAllDt.sum hc hd =>
      FoldObsDt.sum (rotAllDtc_foldObs hc) (rotAllDt_foldObs hd)

end

/-- Rotation is reflexive (constructor level). -/
private theorem rotDtc_refl {s3 : native_String} :
    ∀ c : SmtDatatypeCons, RotDtc s3 c c
  | SmtDatatypeCons.unit => RotDtc.unit
  | SmtDatatypeCons.cons T c => RotDtc.cons (RotTy.same T) (rotDtc_refl c)

/-- Rotation is reflexive. -/
private theorem rotDt_refl {s3 : native_String} :
    ∀ d : SmtDatatype, RotDt s3 d d
  | SmtDatatype.null => RotDt.null
  | SmtDatatype.sum c d => RotDt.sum (rotDtc_refl c) (rotDt_refl d)

/-- Equal sides certify against any positionally aligned guide (constructor
level).  The alignment supplied by `FSkel` is all that is needed: the
type-level certificate for equal sides is `RotAllTy.same` at every guide. -/
private theorem fskel_rotAll_refl_dtc {s3 : native_String} :
    ∀ {cF cH : SmtDatatypeCons}, FSkelDtc cF cH → RotAllDtc s3 cH cF cF
  | _, _, FSkelDtc.unit => RotAllDtc.unit
  | _, _, FSkelDtc.cons _ hc =>
      RotAllDtc.cons (RotAllTy.same _ _) (fskel_rotAll_refl_dtc hc)

/-- Equal sides certify against any positionally aligned guide. -/
private theorem fskel_rotAll_refl_dt {s3 : native_String} :
    ∀ {dF dH : SmtDatatype}, FSkelDt dF dH → RotAllDt s3 dH dF dF
  | _, _, FSkelDt.null => RotAllDt.null
  | _, _, FSkelDt.sum hc hd =>
      RotAllDt.sum (fskel_rotAll_refl_dtc hc) (fskel_rotAll_refl_dt hd)

/-! ### Lift and refill closure of the rotation relation

Folding the OLD side of a rotation pair, and `s3`-refilling the NEW side,
both preserve the relation: every reference a lift places on the old side
is absorbed by `refFlip` (with `refDef_lift_inv` restoring the carried
implication at `s3` nodes), and every body a refill inserts on the new
side sits at an old-side reference (`refFlip` again) or under an `s3`
shield.  These are the two elementary operations by which the two
histories' resolutions differ. -/

mutual

private theorem rot_lift_refl_ty (s3 w : native_String) (V : SmtDatatype) :
    ∀ T : SmtType, RotTy s3 (__smtx_type_lift w V T) T
  | SmtType.Datatype q Z => by
      by_cases hFold : native_Teq (SmtType.Datatype w V)
          (SmtType.Datatype q Z) = true
      · rw [show __smtx_type_lift w V (SmtType.Datatype q Z) =
            SmtType.TypeRef w by simp [__smtx_type_lift, native_ite, hFold]]
        exact RotTy.refFlip
      · rw [show __smtx_type_lift w V (SmtType.Datatype q Z) =
            SmtType.Datatype q (__smtx_dt_lift w V Z) by
          simp [__smtx_type_lift, native_ite, hFold]]
        exact RotTy.dt (rot_lift_refl_dt s3 w V Z)
  | SmtType.TypeRef r => by
      rw [show __smtx_type_lift w V (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.None => by
      rw [show __smtx_type_lift w V SmtType.None = SmtType.None by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Bool => by
      rw [show __smtx_type_lift w V SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Int => by
      rw [show __smtx_type_lift w V SmtType.Int = SmtType.Int by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Real => by
      rw [show __smtx_type_lift w V SmtType.Real = SmtType.Real by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.RegLan => by
      rw [show __smtx_type_lift w V SmtType.RegLan = SmtType.RegLan by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.BitVec n => by
      rw [show __smtx_type_lift w V (SmtType.BitVec n) = SmtType.BitVec n by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Map A B => by
      rw [show __smtx_type_lift w V (SmtType.Map A B) = SmtType.Map A B by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Set A => by
      rw [show __smtx_type_lift w V (SmtType.Set A) = SmtType.Set A by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Seq A => by
      rw [show __smtx_type_lift w V (SmtType.Seq A) = SmtType.Seq A by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.Char => by
      rw [show __smtx_type_lift w V SmtType.Char = SmtType.Char by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.USort u => by
      rw [show __smtx_type_lift w V (SmtType.USort u) = SmtType.USort u by
        simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.FunType A B => by
      rw [show __smtx_type_lift w V (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_lift]]
      exact RotTy.same _
  | SmtType.DtcAppType A B => by
      rw [show __smtx_type_lift w V (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_lift]]
      exact RotTy.same _

private theorem rot_lift_refl_dtc (s3 w : native_String) (V : SmtDatatype) :
    ∀ c : SmtDatatypeCons, RotDtc s3 (__smtx_dtc_lift w V c) c
  | SmtDatatypeCons.unit => by
      rw [show __smtx_dtc_lift w V SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotDtc.unit
  | SmtDatatypeCons.cons T c => by
      rw [show __smtx_dtc_lift w V (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_lift w V T)
            (__smtx_dtc_lift w V c) by simp [__smtx_dtc_lift]]
      exact RotDtc.cons (rot_lift_refl_ty s3 w V T)
        (rot_lift_refl_dtc s3 w V c)

private theorem rot_lift_refl_dt (s3 w : native_String) (V : SmtDatatype) :
    ∀ d : SmtDatatype, RotDt s3 (__smtx_dt_lift w V d) d
  | SmtDatatype.null => by
      rw [show __smtx_dt_lift w V SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotDt.null
  | SmtDatatype.sum c d => by
      rw [show __smtx_dt_lift w V (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_lift w V c) (__smtx_dt_lift w V d) by
        simp [__smtx_dt_lift]]
      exact RotDt.sum (rot_lift_refl_dtc s3 w V c)
        (rot_lift_refl_dt s3 w V d)

end

mutual

private theorem rot_lift_left_ty {s3 : native_String} (w : native_String)
    (V : SmtDatatype) :
    ∀ {TO TN : SmtType}, RotTy s3 TO TN →
      RotTy s3 (__smtx_type_lift w V TO) TN
  | _, _, RotTy.same T => rot_lift_refl_ty s3 w V T
  | _, _, @RotTy.dt _ q ZO ZN hBody => by
      by_cases hFold : native_Teq (SmtType.Datatype w V)
          (SmtType.Datatype q ZO) = true
      · rw [show __smtx_type_lift w V (SmtType.Datatype q ZO) =
            SmtType.TypeRef w by simp [__smtx_type_lift, native_ite, hFold]]
        exact RotTy.refFlip
      · rw [show __smtx_type_lift w V (SmtType.Datatype q ZO) =
            SmtType.Datatype q (__smtx_dt_lift w V ZO) by
          simp [__smtx_type_lift, native_ite, hFold]]
        exact RotTy.dt (rot_lift_left_dt w V hBody)
  | _, _, @RotTy.rot _ ZO ZN hInh => by
      by_cases hFold : native_Teq (SmtType.Datatype w V)
          (SmtType.Datatype s3 ZO) = true
      · rw [show __smtx_type_lift w V (SmtType.Datatype s3 ZO) =
            SmtType.TypeRef w by simp [__smtx_type_lift, native_ite, hFold]]
        exact RotTy.refFlip
      · rw [show __smtx_type_lift w V (SmtType.Datatype s3 ZO) =
            SmtType.Datatype s3 (__smtx_dt_lift w V ZO) by
          simp [__smtx_type_lift, native_ite, hFold]]
        refine RotTy.rot (fun h => hInh ?_)
        exact inhabited_of_refDef_empty s3 ZO
          (refDef_lift_inv_dt w V ZO
            (refDef_empty_of_inhabited s3 (__smtx_dt_lift w V ZO) h))
  | _, _, @RotTy.refFlip _ r TN => by
      rw [show __smtx_type_lift w V (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotTy.refFlip

private theorem rot_lift_left_dtc {s3 : native_String} (w : native_String)
    (V : SmtDatatype) :
    ∀ {cO cN : SmtDatatypeCons}, RotDtc s3 cO cN →
      RotDtc s3 (__smtx_dtc_lift w V cO) cN
  | _, _, RotDtc.unit => by
      rw [show __smtx_dtc_lift w V SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotDtc.unit
  | _, _, @RotDtc.cons _ TO TN cO cN hT hc => by
      rw [show __smtx_dtc_lift w V (SmtDatatypeCons.cons TO cO) =
          SmtDatatypeCons.cons (__smtx_type_lift w V TO)
            (__smtx_dtc_lift w V cO) by simp [__smtx_dtc_lift]]
      exact RotDtc.cons (rot_lift_left_ty w V hT) (rot_lift_left_dtc w V hc)

private theorem rot_lift_left_dt {s3 : native_String} (w : native_String)
    (V : SmtDatatype) :
    ∀ {dO dN : SmtDatatype}, RotDt s3 dO dN →
      RotDt s3 (__smtx_dt_lift w V dO) dN
  | _, _, RotDt.null => by
      rw [show __smtx_dt_lift w V SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotDt.null
  | _, _, @RotDt.sum _ cO cN dO dN hc hd => by
      rw [show __smtx_dt_lift w V (SmtDatatype.sum cO dO) =
          SmtDatatype.sum (__smtx_dtc_lift w V cO) (__smtx_dt_lift w V dO) by
        simp [__smtx_dt_lift]]
      exact RotDt.sum (rot_lift_left_dtc w V hc) (rot_lift_left_dt w V hd)

end

mutual

private theorem rot_subst_refl_ty (s3 : native_String) :
    ∀ (K : SmtDatatype) (T : SmtType),
      RotTy s3 T (__smtx_type_substitute s3 K T)
  | K, SmtType.TypeRef r => by
      cases hr : native_streq s3 r with
      | true =>
          rw [show __smtx_type_substitute s3 K (SmtType.TypeRef r) =
              SmtType.Datatype s3 K by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotTy.refFlip
      | false =>
          rw [show __smtx_type_substitute s3 K (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotTy.same _
  | K, SmtType.Datatype q Z => by
      cases hq : native_streq s3 q with
      | true =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotTy.same _
      | false =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute s3 (__smtx_dt_lift q Z K) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotTy.dt (rot_subst_refl_dt s3 (__smtx_dt_lift q Z K) Z)
  | K, SmtType.None => by
      rw [show __smtx_type_substitute s3 K SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Bool => by
      rw [show __smtx_type_substitute s3 K SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Int => by
      rw [show __smtx_type_substitute s3 K SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Real => by
      rw [show __smtx_type_substitute s3 K SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.RegLan => by
      rw [show __smtx_type_substitute s3 K SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.BitVec n => by
      rw [show __smtx_type_substitute s3 K (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Map A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Set A => by
      rw [show __smtx_type_substitute s3 K (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Seq A => by
      rw [show __smtx_type_substitute s3 K (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.Char => by
      rw [show __smtx_type_substitute s3 K SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.USort u => by
      rw [show __smtx_type_substitute s3 K (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.FunType A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact RotTy.same _
  | K, SmtType.DtcAppType A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact RotTy.same _

private theorem rot_subst_refl_dtc (s3 : native_String) :
    ∀ (K : SmtDatatype) (c : SmtDatatypeCons),
      RotDtc s3 c (__smtx_dtc_substitute s3 K c)
  | K, SmtDatatypeCons.unit => by
      rw [show __smtx_dtc_substitute s3 K SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotDtc.unit
  | K, SmtDatatypeCons.cons T c => by
      rw [show __smtx_dtc_substitute s3 K (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute s3 K T)
            (__smtx_dtc_substitute s3 K c) by simp [__smtx_dtc_substitute]]
      exact RotDtc.cons (rot_subst_refl_ty s3 K T)
        (rot_subst_refl_dtc s3 K c)

private theorem rot_subst_refl_dt (s3 : native_String) :
    ∀ (K : SmtDatatype) (d : SmtDatatype),
      RotDt s3 d (__smtx_dt_substitute s3 K d)
  | K, SmtDatatype.null => by
      rw [show __smtx_dt_substitute s3 K SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotDt.null
  | K, SmtDatatype.sum c d => by
      rw [show __smtx_dt_substitute s3 K (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute s3 K c)
            (__smtx_dt_substitute s3 K d) by simp [__smtx_dt_substitute]]
      exact RotDt.sum (rot_subst_refl_dtc s3 K c)
        (rot_subst_refl_dt s3 K d)

end

mutual

private theorem rot_subst_right_ty {s3 : native_String} :
    ∀ (K : SmtDatatype) {TO TN : SmtType}, RotTy s3 TO TN →
      RotTy s3 TO (__smtx_type_substitute s3 K TN)
  | K, _, _, RotTy.same T => rot_subst_refl_ty s3 K T
  | K, _, _, @RotTy.dt _ q ZO ZN hBody => by
      cases hq : native_streq s3 q with
      | true =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q ZN) =
              SmtType.Datatype q ZN by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotTy.dt hBody
      | false =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q ZN) =
              SmtType.Datatype q
                (__smtx_dt_substitute s3 (__smtx_dt_lift q ZN K) ZN) by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotTy.dt
            (rot_subst_right_dt (__smtx_dt_lift q ZN K) hBody)
  | K, _, _, @RotTy.rot _ ZO ZN hInh => by
      rw [show __smtx_type_substitute s3 K (SmtType.Datatype s3 ZN) =
          SmtType.Datatype s3 ZN by
        simp [__smtx_type_substitute, native_ite, native_streq]]
      exact RotTy.rot hInh
  | K, _, _, @RotTy.refFlip _ r TN => RotTy.refFlip

private theorem rot_subst_right_dtc {s3 : native_String} :
    ∀ (K : SmtDatatype) {cO cN : SmtDatatypeCons}, RotDtc s3 cO cN →
      RotDtc s3 cO (__smtx_dtc_substitute s3 K cN)
  | K, _, _, RotDtc.unit => by
      rw [show __smtx_dtc_substitute s3 K SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotDtc.unit
  | K, _, _, @RotDtc.cons _ TO TN cO cN hT hc => by
      rw [show __smtx_dtc_substitute s3 K (SmtDatatypeCons.cons TN cN) =
          SmtDatatypeCons.cons (__smtx_type_substitute s3 K TN)
            (__smtx_dtc_substitute s3 K cN) by simp [__smtx_dtc_substitute]]
      exact RotDtc.cons (rot_subst_right_ty K hT) (rot_subst_right_dtc K hc)

private theorem rot_subst_right_dt {s3 : native_String} :
    ∀ (K : SmtDatatype) {dO dN : SmtDatatype}, RotDt s3 dO dN →
      RotDt s3 dO (__smtx_dt_substitute s3 K dN)
  | K, _, _, RotDt.null => by
      rw [show __smtx_dt_substitute s3 K SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotDt.null
  | K, _, _, @RotDt.sum _ cO cN dO dN hc hd => by
      rw [show __smtx_dt_substitute s3 K (SmtDatatype.sum cN dN) =
          SmtDatatype.sum (__smtx_dtc_substitute s3 K cN)
            (__smtx_dt_substitute s3 K dN) by simp [__smtx_dt_substitute]]
      exact RotDt.sum (rot_subst_right_dtc K hc) (rot_subst_right_dt K hd)

end

/-! ### Transitivity of rotation

Rotation composes: equal sides are transparent, structural cases recurse,
inhabitedness implications compose (through `rotDt_refDef` when one leg is
structural and the other is a rotation), and an old-side reference absorbs
any continuation.  This is what lets the lift and refill closure rungs
chain through intermediate forms of a resolution. -/

mutual

private theorem rot_trans_ty {s3 : native_String} :
    ∀ {TA TB TC : SmtType}, RotTy s3 TA TB → RotTy s3 TB TC →
      RotTy s3 TA TC
  | _, _, _, RotTy.same _, hBC => hBC
  | _, _, _, RotTy.refFlip, _ => RotTy.refFlip
  | _, _, _, @RotTy.dt _ q ZA ZB hAB, hBC => by
      cases hBC with
      | same => exact RotTy.dt hAB
      | dt hBC' => exact RotTy.dt (rot_trans_dt hAB hBC')
      | rot hInh =>
          exact RotTy.rot (fun h =>
            hInh (inhabited_of_refDef_empty s3 ZB
              (rotDt_refDef hAB
                (refDef_empty_of_inhabited s3 ZA h))))
  | _, _, _, @RotTy.rot _ ZA ZB hInhAB, hBC => by
      cases hBC with
      | same => exact RotTy.rot hInhAB
      | dt hBC' =>
          exact RotTy.rot (fun h =>
            inhabited_of_refDef_empty s3 _
              (rotDt_refDef hBC'
                (refDef_empty_of_inhabited s3 ZB (hInhAB h))))
      | rot hInhBC => exact RotTy.rot (fun h => hInhBC (hInhAB h))

private theorem rot_trans_dtc {s3 : native_String} :
    ∀ {cA cB cC : SmtDatatypeCons}, RotDtc s3 cA cB → RotDtc s3 cB cC →
      RotDtc s3 cA cC
  | _, _, _, RotDtc.unit, hBC => hBC
  | _, _, _, RotDtc.cons hT hc, hBC => by
      cases hBC with
      | cons hT' hc' =>
          exact RotDtc.cons (rot_trans_ty hT hT') (rot_trans_dtc hc hc')

private theorem rot_trans_dt {s3 : native_String} :
    ∀ {dA dB dC : SmtDatatype}, RotDt s3 dA dB → RotDt s3 dB dC →
      RotDt s3 dA dC
  | _, _, _, RotDt.null, hBC => hBC
  | _, _, _, RotDt.sum hc hd, hBC => by
      cases hBC with
      | sum hc' hd' =>
          exact RotDt.sum (rot_trans_dtc hc hc') (rot_trans_dt hd hd')

end

/-! ### Structural rotation and the paired-lift rung

The inhabitedness implications carried at `rot` spots do not survive a
lift pair (each side's lift damages defaultability independently), so the
cascade layer of the establishment works with the *structural* rotation
`RotSh` — the same shape discipline as `Rot` with unconstrained `s3`
bodies — and the implications are re-established against the final
objects separately.

`noFatalB` is the decidable fold-alignment premise of the paired-lift
rung: at every positionally-paired datatype node, if the new-side lift
target would fold the new node, the old-side target must fold the old
node.  Machine sweeps confirm it holds at every lift application arising
in a reachable descent cascade.  Under it, a lift pair with distinct
targets preserves structural rotation: aligned folds collapse to equal
references, old-side-only folds land in `refFlip`, `s3` pairs are
untouched (the lifted name is distinct from `s3`), and everything else
recurses. -/

mutual

private inductive RotShTy (s3 : native_String) : SmtType → SmtType → Prop where
  | same (T : SmtType) : RotShTy s3 T T
  | dt {q : native_String} {ZO ZN : SmtDatatype} :
      RotShDt s3 ZO ZN →
      RotShTy s3 (SmtType.Datatype q ZO) (SmtType.Datatype q ZN)
  | rotAny {ZO ZN : SmtDatatype} :
      RotShTy s3 (SmtType.Datatype s3 ZO) (SmtType.Datatype s3 ZN)
  | refFlip {r : native_String} {TN : SmtType} :
      RotShTy s3 (SmtType.TypeRef r) TN

private inductive RotShDtc (s3 : native_String) :
    SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : RotShDtc s3 SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TO TN : SmtType} {cO cN : SmtDatatypeCons} :
      RotShTy s3 TO TN → RotShDtc s3 cO cN →
      RotShDtc s3 (SmtDatatypeCons.cons TO cO) (SmtDatatypeCons.cons TN cN)

private inductive RotShDt (s3 : native_String) :
    SmtDatatype → SmtDatatype → Prop where
  | null : RotShDt s3 SmtDatatype.null SmtDatatype.null
  | sum {cO cN : SmtDatatypeCons} {dO dN : SmtDatatype} :
      RotShDtc s3 cO cN → RotShDt s3 dO dN →
      RotShDt s3 (SmtDatatype.sum cO dO) (SmtDatatype.sum cN dN)

end

mutual

private def noFatalBTy (s3 v : native_String) (VO VN : SmtDatatype) :
    SmtType → SmtType → native_Bool
  | SmtType.Datatype q WO, SmtType.Datatype q' WN =>
      native_and
        (native_not (native_and
          (native_Teq (SmtType.Datatype v VN) (SmtType.Datatype q' WN))
          (native_not
            (native_Teq (SmtType.Datatype v VO) (SmtType.Datatype q WO)))))
        (native_ite (native_and (native_streq q s3) (native_streq q' s3))
          true (noFatalBDt s3 v VO VN WO WN))
  | _, _ => true

private def noFatalBDtc (s3 v : native_String) (VO VN : SmtDatatype) :
    SmtDatatypeCons → SmtDatatypeCons → native_Bool
  | SmtDatatypeCons.cons TO cO, SmtDatatypeCons.cons TN cN =>
      native_and (noFatalBTy s3 v VO VN TO TN)
        (noFatalBDtc s3 v VO VN cO cN)
  | _, _ => true

private def noFatalBDt (s3 v : native_String) (VO VN : SmtDatatype) :
    SmtDatatype → SmtDatatype → native_Bool
  | SmtDatatype.sum cO dO, SmtDatatype.sum cN dN =>
      native_and (noFatalBDtc s3 v VO VN cO cN)
        (noFatalBDt s3 v VO VN dO dN)
  | _, _ => true

end

private theorem noFatalBTy_parts {s3 v : native_String}
    {VO VN : SmtDatatype} {q q' : native_String} {WO WN : SmtDatatype}
    (h : noFatalBTy s3 v VO VN (SmtType.Datatype q WO)
      (SmtType.Datatype q' WN) = true) :
    (native_Teq (SmtType.Datatype v VN) (SmtType.Datatype q' WN) = true →
      native_Teq (SmtType.Datatype v VO) (SmtType.Datatype q WO) = true) ∧
      (native_and (native_streq q s3) (native_streq q' s3) = false →
        noFatalBDt s3 v VO VN WO WN = true) := by
  simp only [noFatalBTy, native_and, native_not, native_ite] at h
  constructor
  · intro hN
    cases hO : native_Teq (SmtType.Datatype v VO) (SmtType.Datatype q WO) <;>
      simp_all
  · intro hs
    cases hTest : Bool.and (native_streq q s3) (native_streq q' s3) <;>
      simp_all [native_and]

private theorem noFatalBDtc_parts {s3 v : native_String}
    {VO VN : SmtDatatype} {TO TN : SmtType} {cO cN : SmtDatatypeCons}
    (h : noFatalBDtc s3 v VO VN (SmtDatatypeCons.cons TO cO)
      (SmtDatatypeCons.cons TN cN) = true) :
    noFatalBTy s3 v VO VN TO TN = true ∧
      noFatalBDtc s3 v VO VN cO cN = true := by
  simpa [noFatalBDtc, native_and, Bool.and_eq_true] using h

private theorem noFatalBDt_parts {s3 v : native_String}
    {VO VN : SmtDatatype} {cO cN : SmtDatatypeCons} {dO dN : SmtDatatype}
    (h : noFatalBDt s3 v VO VN (SmtDatatype.sum cO dO)
      (SmtDatatype.sum cN dN) = true) :
    noFatalBDtc s3 v VO VN cO cN = true ∧
      noFatalBDt s3 v VO VN dO dN = true := by
  simpa [noFatalBDt, native_and, Bool.and_eq_true] using h

mutual

private theorem rotSh_lift_same_ty {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ T : SmtType, noFatalBTy s3 v VO VN T T = true →
      RotShTy s3 (__smtx_type_lift v VO T) (__smtx_type_lift v VN T)
  | SmtType.Datatype q W, hAlign => by
      have hParts := noFatalBTy_parts hAlign
      by_cases hN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype q W) = true
      · have hO := hParts.1 hN
        rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
        rw [show __smtx_type_lift v VN (SmtType.Datatype q W) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hN]]
        exact RotShTy.same _
      · by_cases hO : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype q W) = true
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
              SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
          exact RotShTy.refFlip
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
              SmtType.Datatype q (__smtx_dt_lift v VO W) by
            simp [__smtx_type_lift, native_ite, hO]]
          rw [show __smtx_type_lift v VN (SmtType.Datatype q W) =
              SmtType.Datatype q (__smtx_dt_lift v VN W) by
            simp [__smtx_type_lift, native_ite, hN]]
          by_cases hq : native_streq q s3 = true
          · have hqs : q = s3 := by simpa [native_streq] using hq
            subst q
            exact RotShTy.rotAny
          · exact RotShTy.dt (rotSh_lift_same_dt v VO VN hvs3 W
              (hParts.2 (by
                cases hqv : native_streq q s3 <;>
                  simp_all [native_and])))
  | SmtType.TypeRef r, _ => by
      rw [show __smtx_type_lift v VO (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotShTy.refFlip
  | SmtType.None, _ => by
      rw [show __smtx_type_lift v VO SmtType.None = SmtType.None by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.None = SmtType.None by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Bool, _ => by
      rw [show __smtx_type_lift v VO SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Int, _ => by
      rw [show __smtx_type_lift v VO SmtType.Int = SmtType.Int by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Int = SmtType.Int by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Real, _ => by
      rw [show __smtx_type_lift v VO SmtType.Real = SmtType.Real by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Real = SmtType.Real by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.RegLan, _ => by
      rw [show __smtx_type_lift v VO SmtType.RegLan = SmtType.RegLan by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.RegLan = SmtType.RegLan by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.BitVec n, _ => by
      rw [show __smtx_type_lift v VO (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Map A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Set A, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Set A) = SmtType.Set A by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Set A) = SmtType.Set A by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Seq A, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Seq A) = SmtType.Seq A by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Seq A) = SmtType.Seq A by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.Char, _ => by
      rw [show __smtx_type_lift v VO SmtType.Char = SmtType.Char by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Char = SmtType.Char by
        simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.USort u, _ => by
      rw [show __smtx_type_lift v VO (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.FunType A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_lift]]
      exact RotShTy.same _
  | SmtType.DtcAppType A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_lift]]
      exact RotShTy.same _

private theorem rotSh_lift_same_dtc {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ c : SmtDatatypeCons, noFatalBDtc s3 v VO VN c c = true →
      RotShDtc s3 (__smtx_dtc_lift v VO c) (__smtx_dtc_lift v VN c)
  | SmtDatatypeCons.unit, _ => by
      rw [show __smtx_dtc_lift v VO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotShDtc.unit
  | SmtDatatypeCons.cons T c, hAlign => by
      have hParts := noFatalBDtc_parts hAlign
      rw [show __smtx_dtc_lift v VO (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_lift v VO T)
            (__smtx_dtc_lift v VO c) by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_lift v VN T)
            (__smtx_dtc_lift v VN c) by simp [__smtx_dtc_lift]]
      exact RotShDtc.cons
        (rotSh_lift_same_ty v VO VN hvs3 T hParts.1)
        (rotSh_lift_same_dtc v VO VN hvs3 c hParts.2)

private theorem rotSh_lift_same_dt {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ d : SmtDatatype, noFatalBDt s3 v VO VN d d = true →
      RotShDt s3 (__smtx_dt_lift v VO d) (__smtx_dt_lift v VN d)
  | SmtDatatype.null, _ => by
      rw [show __smtx_dt_lift v VO SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotShDt.null
  | SmtDatatype.sum c d, hAlign => by
      have hParts := noFatalBDt_parts hAlign
      rw [show __smtx_dt_lift v VO (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_lift v VO c)
            (__smtx_dt_lift v VO d) by simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_lift v VN c)
            (__smtx_dt_lift v VN d) by simp [__smtx_dt_lift]]
      exact RotShDt.sum
        (rotSh_lift_same_dtc v VO VN hvs3 c hParts.1)
        (rotSh_lift_same_dt v VO VN hvs3 d hParts.2)

end

mutual

private theorem rotSh_lift_pair_ty {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ {TO TN : SmtType}, RotShTy s3 TO TN →
      noFatalBTy s3 v VO VN TO TN = true →
      RotShTy s3 (__smtx_type_lift v VO TO) (__smtx_type_lift v VN TN)
  | _, _, RotShTy.same T, hAlign => rotSh_lift_same_ty v VO VN hvs3 T hAlign
  | _, _, @RotShTy.dt _ q ZO ZN hBody, hAlign => by
      have hParts := noFatalBTy_parts hAlign
      by_cases hN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype q ZN) = true
      · have hO := hParts.1 hN
        rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
        rw [show __smtx_type_lift v VN (SmtType.Datatype q ZN) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hN]]
        exact RotShTy.same _
      · by_cases hO : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype q ZO) = true
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
              SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
          exact RotShTy.refFlip
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
              SmtType.Datatype q (__smtx_dt_lift v VO ZO) by
            simp [__smtx_type_lift, native_ite, hO]]
          rw [show __smtx_type_lift v VN (SmtType.Datatype q ZN) =
              SmtType.Datatype q (__smtx_dt_lift v VN ZN) by
            simp [__smtx_type_lift, native_ite, hN]]
          by_cases hq : native_streq q s3 = true
          · have hqs : q = s3 := by simpa [native_streq] using hq
            subst q
            exact RotShTy.rotAny
          · exact RotShTy.dt (rotSh_lift_pair_dt v VO VN hvs3 hBody
              (hParts.2 (by
                cases hqv : native_streq q s3 <;>
                  simp_all [native_and])))
  | _, _, @RotShTy.rotAny _ ZO ZN, hAlign => by
      have hNO : native_Teq (SmtType.Datatype v VO)
          (SmtType.Datatype s3 ZO) = false := by
        cases hT : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype s3 ZO) with
        | false => rfl
        | true =>
            have hp : v = s3 ∧ VO = ZO := by simpa [native_Teq] using hT
            rw [hp.1] at hvs3
            simp [native_streq] at hvs3
      have hNN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype s3 ZN) = false := by
        cases hT : native_Teq (SmtType.Datatype v VN)
            (SmtType.Datatype s3 ZN) with
        | false => rfl
        | true =>
            have hp : v = s3 ∧ VN = ZN := by simpa [native_Teq] using hT
            rw [hp.1] at hvs3
            simp [native_streq] at hvs3
      rw [show __smtx_type_lift v VO (SmtType.Datatype s3 ZO) =
          SmtType.Datatype s3 (__smtx_dt_lift v VO ZO) by
        simp [__smtx_type_lift, native_ite, hNO]]
      rw [show __smtx_type_lift v VN (SmtType.Datatype s3 ZN) =
          SmtType.Datatype s3 (__smtx_dt_lift v VN ZN) by
        simp [__smtx_type_lift, native_ite, hNN]]
      exact RotShTy.rotAny
  | _, _, @RotShTy.refFlip _ r TN, _ => by
      rw [show __smtx_type_lift v VO (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotShTy.refFlip

private theorem rotSh_lift_pair_dtc {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ {cO cN : SmtDatatypeCons}, RotShDtc s3 cO cN →
      noFatalBDtc s3 v VO VN cO cN = true →
      RotShDtc s3 (__smtx_dtc_lift v VO cO) (__smtx_dtc_lift v VN cN)
  | _, _, RotShDtc.unit, _ => by
      rw [show __smtx_dtc_lift v VO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotShDtc.unit
  | _, _, @RotShDtc.cons _ TO TN cO cN hT hc, hAlign => by
      have hParts := noFatalBDtc_parts hAlign
      rw [show __smtx_dtc_lift v VO (SmtDatatypeCons.cons TO cO) =
          SmtDatatypeCons.cons (__smtx_type_lift v VO TO)
            (__smtx_dtc_lift v VO cO) by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN (SmtDatatypeCons.cons TN cN) =
          SmtDatatypeCons.cons (__smtx_type_lift v VN TN)
            (__smtx_dtc_lift v VN cN) by simp [__smtx_dtc_lift]]
      exact RotShDtc.cons
        (rotSh_lift_pair_ty v VO VN hvs3 hT hParts.1)
        (rotSh_lift_pair_dtc v VO VN hvs3 hc hParts.2)

private theorem rotSh_lift_pair_dt {s3 : native_String}
    (v : native_String) (VO VN : SmtDatatype)
    (hvs3 : native_streq v s3 = false) :
    ∀ {dO dN : SmtDatatype}, RotShDt s3 dO dN →
      noFatalBDt s3 v VO VN dO dN = true →
      RotShDt s3 (__smtx_dt_lift v VO dO) (__smtx_dt_lift v VN dN)
  | _, _, RotShDt.null, _ => by
      rw [show __smtx_dt_lift v VO SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotShDt.null
  | _, _, @RotShDt.sum _ cO cN dO dN hc hd, hAlign => by
      have hParts := noFatalBDt_parts hAlign
      rw [show __smtx_dt_lift v VO (SmtDatatype.sum cO dO) =
          SmtDatatype.sum (__smtx_dtc_lift v VO cO)
            (__smtx_dt_lift v VO dO) by simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN (SmtDatatype.sum cN dN) =
          SmtDatatype.sum (__smtx_dtc_lift v VN cN)
            (__smtx_dt_lift v VN dN) by simp [__smtx_dt_lift]]
      exact RotShDt.sum
        (rotSh_lift_pair_dtc v VO VN hvs3 hc hParts.1)
        (rotSh_lift_pair_dt v VO VN hvs3 hd hParts.2)

end

/-! ### Common-target substitution of a rotation pair

Substituting a structurally-rotated payload pair for `w` in a single
common target preserves structural rotation: reference spots for `w`
receive the two payloads directly (`dt`), shields and untouched atoms are
`same`, `s3`-named nodes exit through `rotAny`, and every internal
descent lifts the pair by a common target, which `rotSh_lift_pair`
handles under the cascade of fold-alignment premises collected by
`noFatalCasc`. -/

mutual

private def noFatalCascTy (s3 w : native_String)
    (QO QN : SmtDatatype) : SmtType → native_Bool
  | SmtType.Datatype q Z =>
      native_ite (native_or (native_streq w q) (native_streq q s3)) true
        (native_and (noFatalBDt s3 q Z Z QO QN)
          (noFatalCascDt s3 w (__smtx_dt_lift q Z QO)
            (__smtx_dt_lift q Z QN) Z))
  | _ => true

private def noFatalCascDtc (s3 w : native_String)
    (QO QN : SmtDatatype) : SmtDatatypeCons → native_Bool
  | SmtDatatypeCons.cons T c =>
      native_and (noFatalCascTy s3 w QO QN T)
        (noFatalCascDtc s3 w QO QN c)
  | SmtDatatypeCons.unit => true

private def noFatalCascDt (s3 w : native_String)
    (QO QN : SmtDatatype) : SmtDatatype → native_Bool
  | SmtDatatype.sum c d =>
      native_and (noFatalCascDtc s3 w QO QN c)
        (noFatalCascDt s3 w QO QN d)
  | SmtDatatype.null => true

end

mutual

private theorem rotSh_subst_common_ty {s3 : native_String}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (T : SmtType) (QO QN : SmtDatatype), RotShDt s3 QO QN →
      noFatalCascTy s3 w QO QN T = true →
      RotShTy s3 (__smtx_type_substitute w QO T)
        (__smtx_type_substitute w QN T)
  | SmtType.TypeRef r, QO, QN, hPair, _ => by
      cases hr : native_streq w r with
      | true =>
          rw [show __smtx_type_substitute w QO (SmtType.TypeRef r) =
              SmtType.Datatype w QO by
            simp [__smtx_type_substitute, native_ite, hr]]
          rw [show __smtx_type_substitute w QN (SmtType.TypeRef r) =
              SmtType.Datatype w QN by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShTy.dt hPair
      | false =>
          rw [show __smtx_type_substitute w QO (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          rw [show __smtx_type_substitute w QN (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShTy.same _
  | SmtType.Datatype q Z, QO, QN, hPair, hCasc => by
      cases hq : native_streq w q with
      | true =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotShTy.same _
      | false =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q Z QO) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q Z QN) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          cases hqs : native_streq q s3 with
          | true =>
              have hq3 : q = s3 := by simpa [native_streq] using hqs
              subst q
              exact RotShTy.rotAny
          | false =>
              have hCascParts :
                  noFatalBDt s3 q Z Z QO QN = true ∧
                    noFatalCascDt s3 w (__smtx_dt_lift q Z QO)
                      (__smtx_dt_lift q Z QN) Z = true := by
                simp only [noFatalCascTy, native_ite, native_or, native_and,
                  hq, hqs] at hCasc
                simpa [Bool.and_eq_true] using hCasc
              exact RotShTy.dt (rotSh_subst_common_dt w hws3 Z
                (__smtx_dt_lift q Z QO) (__smtx_dt_lift q Z QN)
                (rotSh_lift_pair_dt q Z Z hqs hPair hCascParts.1)
                hCascParts.2)
  | SmtType.None, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Bool, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Int, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Real, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.RegLan, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.BitVec n, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Map A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Set A, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Seq A, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.Char, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.USort u, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.FunType A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | SmtType.DtcAppType A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _

private theorem rotSh_subst_common_dtc {s3 : native_String}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (c : SmtDatatypeCons) (QO QN : SmtDatatype), RotShDt s3 QO QN →
      noFatalCascDtc s3 w QO QN c = true →
      RotShDtc s3 (__smtx_dtc_substitute w QO c)
        (__smtx_dtc_substitute w QN c)
  | SmtDatatypeCons.unit, QO, QN, _, _ => by
      rw [show __smtx_dtc_substitute w QO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotShDtc.unit
  | SmtDatatypeCons.cons T c, QO, QN, hPair, hCasc => by
      have hParts :
          noFatalCascTy s3 w QO QN T = true ∧
            noFatalCascDtc s3 w QO QN c = true := by
        simpa [noFatalCascDtc, native_and, Bool.and_eq_true] using hCasc
      rw [show __smtx_dtc_substitute w QO (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QO T)
            (__smtx_dtc_substitute w QO c) by simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QN T)
            (__smtx_dtc_substitute w QN c) by simp [__smtx_dtc_substitute]]
      exact RotShDtc.cons
        (rotSh_subst_common_ty w hws3 T QO QN hPair hParts.1)
        (rotSh_subst_common_dtc w hws3 c QO QN hPair hParts.2)

private theorem rotSh_subst_common_dt {s3 : native_String}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (d : SmtDatatype) (QO QN : SmtDatatype), RotShDt s3 QO QN →
      noFatalCascDt s3 w QO QN d = true →
      RotShDt s3 (__smtx_dt_substitute w QO d)
        (__smtx_dt_substitute w QN d)
  | SmtDatatype.null, QO, QN, _, _ => by
      rw [show __smtx_dt_substitute w QO SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotShDt.null
  | SmtDatatype.sum c d, QO, QN, hPair, hCasc => by
      have hParts :
          noFatalCascDtc s3 w QO QN c = true ∧
            noFatalCascDt s3 w QO QN d = true := by
        simpa [noFatalCascDt, native_and, Bool.and_eq_true] using hCasc
      rw [show __smtx_dt_substitute w QO (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute w QO c)
            (__smtx_dt_substitute w QO d) by simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute w QN c)
            (__smtx_dt_substitute w QN d) by simp [__smtx_dt_substitute]]
      exact RotShDt.sum
        (rotSh_subst_common_dtc w hws3 c QO QN hPair hParts.1)
        (rotSh_subst_common_dt w hws3 d QO QN hPair hParts.2)

end

/-! ### Pre-refill rotation and the refill step

Before the appended `s3` entry substitutes, the two partial chain states
relate by `RotShPre`: structural rotation whose new side still carries
`@s3` holes where the old side has `s3` nodes (`preRot`), and whose
reference flips are confined to a set of *dead* names (`flip`) — names no
remaining substitution touches.  Machine sweeps show flips arise at the
shielded head name and at already-processed entry names, whose references
are bound once their node is created; the dead set grows monotonically as
the chain applies.  The final `s3` substitution (`s3` is never dead while
pending) converts every `preRot` hole into a refilled `s3` node and turns
dead flips into ordinary `refFlip`s, yielding plain structural rotation. -/

mutual

private theorem rotSh_subst_refl_ty (s3 : native_String) :
    ∀ (K : SmtDatatype) (T : SmtType),
      RotShTy s3 T (__smtx_type_substitute s3 K T)
  | K, SmtType.TypeRef r => by
      cases hr : native_streq s3 r with
      | true =>
          rw [show __smtx_type_substitute s3 K (SmtType.TypeRef r) =
              SmtType.Datatype s3 K by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShTy.refFlip
      | false =>
          rw [show __smtx_type_substitute s3 K (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShTy.same _
  | K, SmtType.Datatype q Z => by
      cases hq : native_streq s3 q with
      | true =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotShTy.same _
      | false =>
          rw [show __smtx_type_substitute s3 K (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute s3 (__smtx_dt_lift q Z K) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotShTy.dt
            (rotSh_subst_refl_dt s3 (__smtx_dt_lift q Z K) Z)
  | K, SmtType.None => by
      rw [show __smtx_type_substitute s3 K SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Bool => by
      rw [show __smtx_type_substitute s3 K SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Int => by
      rw [show __smtx_type_substitute s3 K SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Real => by
      rw [show __smtx_type_substitute s3 K SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.RegLan => by
      rw [show __smtx_type_substitute s3 K SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.BitVec n => by
      rw [show __smtx_type_substitute s3 K (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Map A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Set A => by
      rw [show __smtx_type_substitute s3 K (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Seq A => by
      rw [show __smtx_type_substitute s3 K (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.Char => by
      rw [show __smtx_type_substitute s3 K SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.USort u => by
      rw [show __smtx_type_substitute s3 K (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.FunType A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _
  | K, SmtType.DtcAppType A B => by
      rw [show __smtx_type_substitute s3 K (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact RotShTy.same _

private theorem rotSh_subst_refl_dtc (s3 : native_String) :
    ∀ (K : SmtDatatype) (c : SmtDatatypeCons),
      RotShDtc s3 c (__smtx_dtc_substitute s3 K c)
  | K, SmtDatatypeCons.unit => by
      rw [show __smtx_dtc_substitute s3 K SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotShDtc.unit
  | K, SmtDatatypeCons.cons T c => by
      rw [show __smtx_dtc_substitute s3 K (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute s3 K T)
            (__smtx_dtc_substitute s3 K c) by
        simp [__smtx_dtc_substitute]]
      exact RotShDtc.cons (rotSh_subst_refl_ty s3 K T)
        (rotSh_subst_refl_dtc s3 K c)

private theorem rotSh_subst_refl_dt (s3 : native_String) :
    ∀ (K : SmtDatatype) (d : SmtDatatype),
      RotShDt s3 d (__smtx_dt_substitute s3 K d)
  | K, SmtDatatype.null => by
      rw [show __smtx_dt_substitute s3 K SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotShDt.null
  | K, SmtDatatype.sum c d => by
      rw [show __smtx_dt_substitute s3 K (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute s3 K c)
            (__smtx_dt_substitute s3 K d) by
        simp [__smtx_dt_substitute]]
      exact RotShDt.sum (rotSh_subst_refl_dtc s3 K c)
        (rotSh_subst_refl_dt s3 K d)

end

mutual

private inductive RotShPreTy (s3 : native_String)
    (dead : native_String → native_Bool) : SmtType → SmtType → Prop where
  | same (T : SmtType) : RotShPreTy s3 dead T T
  | dt {q : native_String} {ZO ZN : SmtDatatype} :
      native_streq q s3 = false →
      RotShPreDt s3 dead ZO ZN →
      RotShPreTy s3 dead (SmtType.Datatype q ZO) (SmtType.Datatype q ZN)
  | rotAny {ZO ZN : SmtDatatype} :
      RotShPreTy s3 dead (SmtType.Datatype s3 ZO) (SmtType.Datatype s3 ZN)
  | preRot {ZO : SmtDatatype} :
      RotShPreTy s3 dead (SmtType.Datatype s3 ZO) (SmtType.TypeRef s3)
  | flip {r : native_String} {TN : SmtType} :
      dead r = true →
      RotShPreTy s3 dead (SmtType.TypeRef r) TN

private inductive RotShPreDtc (s3 : native_String)
    (dead : native_String → native_Bool) :
    SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : RotShPreDtc s3 dead SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TO TN : SmtType} {cO cN : SmtDatatypeCons} :
      RotShPreTy s3 dead TO TN → RotShPreDtc s3 dead cO cN →
      RotShPreDtc s3 dead (SmtDatatypeCons.cons TO cO)
        (SmtDatatypeCons.cons TN cN)

private inductive RotShPreDt (s3 : native_String)
    (dead : native_String → native_Bool) :
    SmtDatatype → SmtDatatype → Prop where
  | null : RotShPreDt s3 dead SmtDatatype.null SmtDatatype.null
  | sum {cO cN : SmtDatatypeCons} {dO dN : SmtDatatype} :
      RotShPreDtc s3 dead cO cN → RotShPreDt s3 dead dO dN →
      RotShPreDt s3 dead (SmtDatatype.sum cO dO) (SmtDatatype.sum cN dN)

end

mutual

private theorem rotShPre_refill_ty {s3 : native_String}
    {dead : native_String → native_Bool} :
    ∀ (K : SmtDatatype) {TO TN : SmtType}, RotShPreTy s3 dead TO TN →
      RotShTy s3 TO (__smtx_type_substitute s3 K TN)
  | K, _, _, RotShPreTy.same T => rotSh_subst_refl_ty s3 K T
  | K, _, _, @RotShPreTy.dt _ _ q ZO ZN hq hBody => by
      rw [show __smtx_type_substitute s3 K (SmtType.Datatype q ZN) =
          SmtType.Datatype q
            (__smtx_dt_substitute s3 (__smtx_dt_lift q ZN K) ZN) by
        simp [__smtx_type_substitute, native_ite,
          show native_streq s3 q = false by
            simpa [native_streq, eq_comm] using hq]]
      exact RotShTy.dt
        (rotShPre_refill_dt (__smtx_dt_lift q ZN K) hBody)
  | K, _, _, @RotShPreTy.rotAny _ _ ZO ZN => by
      rw [show __smtx_type_substitute s3 K (SmtType.Datatype s3 ZN) =
          SmtType.Datatype s3 ZN by
        simp [__smtx_type_substitute, native_ite, native_streq]]
      exact RotShTy.rotAny
  | K, _, _, @RotShPreTy.preRot _ _ ZO => by
      rw [show __smtx_type_substitute s3 K (SmtType.TypeRef s3) =
          SmtType.Datatype s3 K by
        simp [__smtx_type_substitute, native_ite, native_streq]]
      exact RotShTy.rotAny
  | K, _, _, @RotShPreTy.flip _ _ r TN _ => RotShTy.refFlip

private theorem rotShPre_refill_dtc {s3 : native_String}
    {dead : native_String → native_Bool} :
    ∀ (K : SmtDatatype) {cO cN : SmtDatatypeCons}, RotShPreDtc s3 dead cO cN →
      RotShDtc s3 cO (__smtx_dtc_substitute s3 K cN)
  | K, _, _, RotShPreDtc.unit => by
      rw [show __smtx_dtc_substitute s3 K SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotShDtc.unit
  | K, _, _, @RotShPreDtc.cons _ _ TO TN cO cN hT hc => by
      rw [show __smtx_dtc_substitute s3 K (SmtDatatypeCons.cons TN cN) =
          SmtDatatypeCons.cons (__smtx_type_substitute s3 K TN)
            (__smtx_dtc_substitute s3 K cN) by
        simp [__smtx_dtc_substitute]]
      exact RotShDtc.cons (rotShPre_refill_ty K hT)
        (rotShPre_refill_dtc K hc)

private theorem rotShPre_refill_dt {s3 : native_String}
    {dead : native_String → native_Bool} :
    ∀ (K : SmtDatatype) {dO dN : SmtDatatype}, RotShPreDt s3 dead dO dN →
      RotShDt s3 dO (__smtx_dt_substitute s3 K dN)
  | K, _, _, RotShPreDt.null => by
      rw [show __smtx_dt_substitute s3 K SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotShDt.null
  | K, _, _, @RotShPreDt.sum _ _ cO cN dO dN hc hd => by
      rw [show __smtx_dt_substitute s3 K (SmtDatatype.sum cN dN) =
          SmtDatatype.sum (__smtx_dtc_substitute s3 K cN)
            (__smtx_dt_substitute s3 K dN) by
        simp [__smtx_dt_substitute]]
      exact RotShDt.sum (rotShPre_refill_dtc K hc)
        (rotShPre_refill_dt K hd)

end

/-! ### Lift rungs for pre-refill rotation

A paired lift over a pre-refill pair: aligned folds collapse to equal
references, old-side-only folds become `flip`s (requiring the lifted name
dead — at use sites interior lift names are never the pending entry, by
the substitution shield, nor `s3`, by the `rotAny` exit, and never a
pending entry name by the `ChainNoDt` facts), `s3` pairs and holes are
untouched, dead flips persist, and everything else recurses. -/

mutual

private theorem rotShPre_lift_same_ty {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ T : SmtType, noFatalBTy s3 v VO VN T T = true →
      RotShPreTy s3 dead (__smtx_type_lift v VO T) (__smtx_type_lift v VN T)
  | SmtType.Datatype q W, hAlign => by
      have hParts := noFatalBTy_parts hAlign
      by_cases hN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype q W) = true
      · have hO := hParts.1 hN
        rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
        rw [show __smtx_type_lift v VN (SmtType.Datatype q W) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hN]]
        exact RotShPreTy.same _
      · by_cases hO : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype q W) = true
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
              SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
          exact RotShPreTy.flip hvdead
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q W) =
              SmtType.Datatype q (__smtx_dt_lift v VO W) by
            simp [__smtx_type_lift, native_ite, hO]]
          rw [show __smtx_type_lift v VN (SmtType.Datatype q W) =
              SmtType.Datatype q (__smtx_dt_lift v VN W) by
            simp [__smtx_type_lift, native_ite, hN]]
          by_cases hq : native_streq q s3 = true
          · have hqs : q = s3 := by simpa [native_streq] using hq
            subst q
            exact RotShPreTy.rotAny
          · have hqf : native_streq q s3 = false := by
              cases hqv : native_streq q s3 <;> simp_all
            exact RotShPreTy.dt hqf
              (rotShPre_lift_same_dt v VO VN hvdead hvs3 W
                (hParts.2 (by simp [native_and, hqf])))
  | SmtType.TypeRef r, _ => by
      rw [show __smtx_type_lift v VO (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.None, _ => by
      rw [show __smtx_type_lift v VO SmtType.None = SmtType.None by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.None = SmtType.None by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Bool, _ => by
      rw [show __smtx_type_lift v VO SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Int, _ => by
      rw [show __smtx_type_lift v VO SmtType.Int = SmtType.Int by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Int = SmtType.Int by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Real, _ => by
      rw [show __smtx_type_lift v VO SmtType.Real = SmtType.Real by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Real = SmtType.Real by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.RegLan, _ => by
      rw [show __smtx_type_lift v VO SmtType.RegLan = SmtType.RegLan by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.RegLan = SmtType.RegLan by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.BitVec n, _ => by
      rw [show __smtx_type_lift v VO (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Map A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Set A, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Set A) = SmtType.Set A by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Set A) = SmtType.Set A by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Seq A, _ => by
      rw [show __smtx_type_lift v VO (SmtType.Seq A) = SmtType.Seq A by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.Seq A) = SmtType.Seq A by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.Char, _ => by
      rw [show __smtx_type_lift v VO SmtType.Char = SmtType.Char by
        simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN SmtType.Char = SmtType.Char by
        simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.USort u, _ => by
      rw [show __smtx_type_lift v VO (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.FunType A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_lift]]
      exact RotShPreTy.same _
  | SmtType.DtcAppType A B, _ => by
      rw [show __smtx_type_lift v VO (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_lift]]
      rw [show __smtx_type_lift v VN (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_lift]]
      exact RotShPreTy.same _

private theorem rotShPre_lift_same_dtc {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ c : SmtDatatypeCons, noFatalBDtc s3 v VO VN c c = true →
      RotShPreDtc s3 dead (__smtx_dtc_lift v VO c) (__smtx_dtc_lift v VN c)
  | SmtDatatypeCons.unit, _ => by
      rw [show __smtx_dtc_lift v VO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotShPreDtc.unit
  | SmtDatatypeCons.cons T c, hAlign => by
      have hParts := noFatalBDtc_parts hAlign
      rw [show __smtx_dtc_lift v VO (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_lift v VO T)
            (__smtx_dtc_lift v VO c) by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_lift v VN T)
            (__smtx_dtc_lift v VN c) by simp [__smtx_dtc_lift]]
      exact RotShPreDtc.cons
        (rotShPre_lift_same_ty v VO VN hvdead hvs3 T hParts.1)
        (rotShPre_lift_same_dtc v VO VN hvdead hvs3 c hParts.2)

private theorem rotShPre_lift_same_dt {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ d : SmtDatatype, noFatalBDt s3 v VO VN d d = true →
      RotShPreDt s3 dead (__smtx_dt_lift v VO d) (__smtx_dt_lift v VN d)
  | SmtDatatype.null, _ => by
      rw [show __smtx_dt_lift v VO SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotShPreDt.null
  | SmtDatatype.sum c d, hAlign => by
      have hParts := noFatalBDt_parts hAlign
      rw [show __smtx_dt_lift v VO (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_lift v VO c)
            (__smtx_dt_lift v VO d) by simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_lift v VN c)
            (__smtx_dt_lift v VN d) by simp [__smtx_dt_lift]]
      exact RotShPreDt.sum
        (rotShPre_lift_same_dtc v VO VN hvdead hvs3 c hParts.1)
        (rotShPre_lift_same_dt v VO VN hvdead hvs3 d hParts.2)

end

mutual

private theorem rotShPre_lift_pair_ty {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ {TO TN : SmtType}, RotShPreTy s3 dead TO TN →
      noFatalBTy s3 v VO VN TO TN = true →
      RotShPreTy s3 dead (__smtx_type_lift v VO TO)
        (__smtx_type_lift v VN TN)
  | _, _, RotShPreTy.same T, hAlign =>
      rotShPre_lift_same_ty v VO VN hvdead hvs3 T hAlign
  | _, _, @RotShPreTy.dt _ _ q ZO ZN hq hBody, hAlign => by
      have hParts := noFatalBTy_parts hAlign
      by_cases hN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype q ZN) = true
      · have hO := hParts.1 hN
        rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
        rw [show __smtx_type_lift v VN (SmtType.Datatype q ZN) =
            SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hN]]
        exact RotShPreTy.same _
      · by_cases hO : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype q ZO) = true
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
              SmtType.TypeRef v by simp [__smtx_type_lift, native_ite, hO]]
          exact RotShPreTy.flip hvdead
        · rw [show __smtx_type_lift v VO (SmtType.Datatype q ZO) =
              SmtType.Datatype q (__smtx_dt_lift v VO ZO) by
            simp [__smtx_type_lift, native_ite, hO]]
          rw [show __smtx_type_lift v VN (SmtType.Datatype q ZN) =
              SmtType.Datatype q (__smtx_dt_lift v VN ZN) by
            simp [__smtx_type_lift, native_ite, hN]]
          exact RotShPreTy.dt hq
            (rotShPre_lift_pair_dt v VO VN hvdead hvs3 hBody
              (hParts.2 (by simp [native_and, hq])))
  | _, _, @RotShPreTy.rotAny _ _ ZO ZN, _ => by
      have hNO : native_Teq (SmtType.Datatype v VO)
          (SmtType.Datatype s3 ZO) = false := by
        cases hT : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype s3 ZO) with
        | false => rfl
        | true =>
            have hp : v = s3 ∧ VO = ZO := by simpa [native_Teq] using hT
            rw [hp.1] at hvs3
            simp [native_streq] at hvs3
      have hNN : native_Teq (SmtType.Datatype v VN)
          (SmtType.Datatype s3 ZN) = false := by
        cases hT : native_Teq (SmtType.Datatype v VN)
            (SmtType.Datatype s3 ZN) with
        | false => rfl
        | true =>
            have hp : v = s3 ∧ VN = ZN := by simpa [native_Teq] using hT
            rw [hp.1] at hvs3
            simp [native_streq] at hvs3
      rw [show __smtx_type_lift v VO (SmtType.Datatype s3 ZO) =
          SmtType.Datatype s3 (__smtx_dt_lift v VO ZO) by
        simp [__smtx_type_lift, native_ite, hNO]]
      rw [show __smtx_type_lift v VN (SmtType.Datatype s3 ZN) =
          SmtType.Datatype s3 (__smtx_dt_lift v VN ZN) by
        simp [__smtx_type_lift, native_ite, hNN]]
      exact RotShPreTy.rotAny
  | _, _, @RotShPreTy.preRot _ _ ZO, _ => by
      have hNO : native_Teq (SmtType.Datatype v VO)
          (SmtType.Datatype s3 ZO) = false := by
        cases hT : native_Teq (SmtType.Datatype v VO)
            (SmtType.Datatype s3 ZO) with
        | false => rfl
        | true =>
            have hp : v = s3 ∧ VO = ZO := by simpa [native_Teq] using hT
            rw [hp.1] at hvs3
            simp [native_streq] at hvs3
      rw [show __smtx_type_lift v VO (SmtType.Datatype s3 ZO) =
          SmtType.Datatype s3 (__smtx_dt_lift v VO ZO) by
        simp [__smtx_type_lift, native_ite, hNO]]
      rw [show __smtx_type_lift v VN (SmtType.TypeRef s3) =
          SmtType.TypeRef s3 by simp [__smtx_type_lift]]
      exact RotShPreTy.preRot
  | _, _, @RotShPreTy.flip _ _ r TN hr, _ => by
      rw [show __smtx_type_lift v VO (SmtType.TypeRef r) =
          SmtType.TypeRef r by simp [__smtx_type_lift]]
      exact RotShPreTy.flip hr

private theorem rotShPre_lift_pair_dtc {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ {cO cN : SmtDatatypeCons}, RotShPreDtc s3 dead cO cN →
      noFatalBDtc s3 v VO VN cO cN = true →
      RotShPreDtc s3 dead (__smtx_dtc_lift v VO cO)
        (__smtx_dtc_lift v VN cN)
  | _, _, RotShPreDtc.unit, _ => by
      rw [show __smtx_dtc_lift v VO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_lift]]
      exact RotShPreDtc.unit
  | _, _, @RotShPreDtc.cons _ _ TO TN cO cN hT hc, hAlign => by
      have hParts := noFatalBDtc_parts hAlign
      rw [show __smtx_dtc_lift v VO (SmtDatatypeCons.cons TO cO) =
          SmtDatatypeCons.cons (__smtx_type_lift v VO TO)
            (__smtx_dtc_lift v VO cO) by simp [__smtx_dtc_lift]]
      rw [show __smtx_dtc_lift v VN (SmtDatatypeCons.cons TN cN) =
          SmtDatatypeCons.cons (__smtx_type_lift v VN TN)
            (__smtx_dtc_lift v VN cN) by simp [__smtx_dtc_lift]]
      exact RotShPreDtc.cons
        (rotShPre_lift_pair_ty v VO VN hvdead hvs3 hT hParts.1)
        (rotShPre_lift_pair_dtc v VO VN hvdead hvs3 hc hParts.2)

private theorem rotShPre_lift_pair_dt {s3 : native_String}
    {dead : native_String → native_Bool}
    (v : native_String) (VO VN : SmtDatatype)
    (hvdead : dead v = true) (hvs3 : native_streq v s3 = false) :
    ∀ {dO dN : SmtDatatype}, RotShPreDt s3 dead dO dN →
      noFatalBDt s3 v VO VN dO dN = true →
      RotShPreDt s3 dead (__smtx_dt_lift v VO dO) (__smtx_dt_lift v VN dN)
  | _, _, RotShPreDt.null, _ => by
      rw [show __smtx_dt_lift v VO SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_lift]]
      exact RotShPreDt.null
  | _, _, @RotShPreDt.sum _ _ cO cN dO dN hc hd, hAlign => by
      have hParts := noFatalBDt_parts hAlign
      rw [show __smtx_dt_lift v VO (SmtDatatype.sum cO dO) =
          SmtDatatype.sum (__smtx_dtc_lift v VO cO)
            (__smtx_dt_lift v VO dO) by simp [__smtx_dt_lift]]
      rw [show __smtx_dt_lift v VN (SmtDatatype.sum cN dN) =
          SmtDatatype.sum (__smtx_dtc_lift v VN cN)
            (__smtx_dt_lift v VN dN) by simp [__smtx_dt_lift]]
      exact RotShPreDt.sum
        (rotShPre_lift_pair_dtc v VO VN hvdead hvs3 hc hParts.1)
        (rotShPre_lift_pair_dt v VO VN hvdead hvs3 hd hParts.2)

end

/-! ### Paired substitution of pre-refill pairs

One chain step substitutes an entry's paired payloads into the paired
accumulators.  `preCascPair` collects, along the paired trees, the
deadness and fold-alignment conditions for every interior lift the
substitution performs; regions under `s3` pairs, holes, shields and dead
flips need nothing.  The step preserves pre-refill rotation: payload
insertion at the entry's references is a `dt` node, shields and dead
flips are untouched (the entry name is live, so it is distinct from
every flip name), and interior descents dispatch into the paired-lift
rung. -/

mutual

private def preCascPairTy (s3 w : native_String)
    (dead : native_String → native_Bool) (QO QN : SmtDatatype) :
    SmtType → SmtType → native_Bool
  | SmtType.Datatype q ZO, SmtType.Datatype _q' ZN =>
      native_ite (native_or (native_streq w q) (native_streq q s3)) true
        (native_and (dead q)
          (native_and (noFatalBDt s3 q ZO ZN QO QN)
            (preCascPairDt s3 w dead (__smtx_dt_lift q ZO QO)
              (__smtx_dt_lift q ZN QN) ZO ZN)))
  | _, _ => true

private def preCascPairDtc (s3 w : native_String)
    (dead : native_String → native_Bool) (QO QN : SmtDatatype) :
    SmtDatatypeCons → SmtDatatypeCons → native_Bool
  | SmtDatatypeCons.cons TO cO, SmtDatatypeCons.cons TN cN =>
      native_and (preCascPairTy s3 w dead QO QN TO TN)
        (preCascPairDtc s3 w dead QO QN cO cN)
  | _, _ => true

private def preCascPairDt (s3 w : native_String)
    (dead : native_String → native_Bool) (QO QN : SmtDatatype) :
    SmtDatatype → SmtDatatype → native_Bool
  | SmtDatatype.sum cO dO, SmtDatatype.sum cN dN =>
      native_and (preCascPairDtc s3 w dead QO QN cO cN)
        (preCascPairDt s3 w dead QO QN dO dN)
  | _, _ => true

end

private theorem preCascPairTy_parts {s3 w : native_String}
    {dead : native_String → native_Bool} {QO QN : SmtDatatype}
    {q q' : native_String} {ZO ZN : SmtDatatype}
    (hw : native_streq w q = false) (hs : native_streq q s3 = false)
    (h : preCascPairTy s3 w dead QO QN (SmtType.Datatype q ZO)
      (SmtType.Datatype q' ZN) = true) :
    dead q = true ∧ noFatalBDt s3 q ZO ZN QO QN = true ∧
      preCascPairDt s3 w dead (__smtx_dt_lift q ZO QO)
        (__smtx_dt_lift q ZN QN) ZO ZN = true := by
  simp only [preCascPairTy, native_ite, native_or, native_and, hw, hs] at h
  simpa [Bool.and_eq_true] using h

private theorem preCascPairDtc_parts {s3 w : native_String}
    {dead : native_String → native_Bool} {QO QN : SmtDatatype}
    {TO TN : SmtType} {cO cN : SmtDatatypeCons}
    (h : preCascPairDtc s3 w dead QO QN (SmtDatatypeCons.cons TO cO)
      (SmtDatatypeCons.cons TN cN) = true) :
    preCascPairTy s3 w dead QO QN TO TN = true ∧
      preCascPairDtc s3 w dead QO QN cO cN = true := by
  simpa [preCascPairDtc, native_and, Bool.and_eq_true] using h

private theorem preCascPairDt_parts {s3 w : native_String}
    {dead : native_String → native_Bool} {QO QN : SmtDatatype}
    {cO cN : SmtDatatypeCons} {dO dN : SmtDatatype}
    (h : preCascPairDt s3 w dead QO QN (SmtDatatype.sum cO dO)
      (SmtDatatype.sum cN dN) = true) :
    preCascPairDtc s3 w dead QO QN cO cN = true ∧
      preCascPairDt s3 w dead QO QN dO dN = true := by
  simpa [preCascPairDt, native_and, Bool.and_eq_true] using h

mutual

private theorem rotShPre_subst_common_ty {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (T : SmtType) (QO QN : SmtDatatype), RotShPreDt s3 dead QO QN →
      preCascPairTy s3 w dead QO QN T T = true →
      RotShPreTy s3 dead (__smtx_type_substitute w QO T)
        (__smtx_type_substitute w QN T)
  | SmtType.TypeRef r, QO, QN, hPair, _ => by
      cases hr : native_streq w r with
      | true =>
          rw [show __smtx_type_substitute w QO (SmtType.TypeRef r) =
              SmtType.Datatype w QO by
            simp [__smtx_type_substitute, native_ite, hr]]
          rw [show __smtx_type_substitute w QN (SmtType.TypeRef r) =
              SmtType.Datatype w QN by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShPreTy.dt hws3 hPair
      | false =>
          rw [show __smtx_type_substitute w QO (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          rw [show __smtx_type_substitute w QN (SmtType.TypeRef r) =
              SmtType.TypeRef r by
            simp [__smtx_type_substitute, native_ite, hr]]
          exact RotShPreTy.same _
  | SmtType.Datatype q Z, QO, QN, hPair, hCasc => by
      cases hq : native_streq w q with
      | true =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q Z) =
              SmtType.Datatype q Z by
            simp [__smtx_type_substitute, native_ite, hq]]
          exact RotShPreTy.same _
      | false =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q Z QO) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q Z) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q Z QN) Z) by
            simp [__smtx_type_substitute, native_ite, hq]]
          cases hqs : native_streq q s3 with
          | true =>
              have hq3 : q = s3 := by simpa [native_streq] using hqs
              subst q
              exact RotShPreTy.rotAny
          | false =>
              have hParts := preCascPairTy_parts hq hqs hCasc
              exact RotShPreTy.dt hqs
                (rotShPre_subst_common_dt w hws3 Z
                  (__smtx_dt_lift q Z QO) (__smtx_dt_lift q Z QN)
                  (rotShPre_lift_pair_dt q Z Z hParts.1 hqs hPair
                    hParts.2.1)
                  hParts.2.2)
  | SmtType.None, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.None = SmtType.None by
        simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Bool, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Bool = SmtType.Bool by
        simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Int, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Int = SmtType.Int by
        simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Real, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Real = SmtType.Real by
        simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.RegLan, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.RegLan =
          SmtType.RegLan by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.BitVec n, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.BitVec n) =
          SmtType.BitVec n by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Map A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Map A B) =
          SmtType.Map A B by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Set A, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Set A) =
          SmtType.Set A by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Seq A, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.Seq A) =
          SmtType.Seq A by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.Char, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN SmtType.Char = SmtType.Char by
        simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.USort u, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.USort u) =
          SmtType.USort u by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.FunType A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _
  | SmtType.DtcAppType A B, QO, QN, _, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      rw [show __smtx_type_substitute w QN (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact RotShPreTy.same _

private theorem rotShPre_subst_common_dtc {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (c : SmtDatatypeCons) (QO QN : SmtDatatype),
      RotShPreDt s3 dead QO QN →
      preCascPairDtc s3 w dead QO QN c c = true →
      RotShPreDtc s3 dead (__smtx_dtc_substitute w QO c)
        (__smtx_dtc_substitute w QN c)
  | SmtDatatypeCons.unit, QO, QN, _, _ => by
      rw [show __smtx_dtc_substitute w QO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotShPreDtc.unit
  | SmtDatatypeCons.cons T c, QO, QN, hPair, hCasc => by
      have hParts := preCascPairDtc_parts hCasc
      rw [show __smtx_dtc_substitute w QO (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QO T)
            (__smtx_dtc_substitute w QO c) by
        simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN (SmtDatatypeCons.cons T c) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QN T)
            (__smtx_dtc_substitute w QN c) by
        simp [__smtx_dtc_substitute]]
      exact RotShPreDtc.cons
        (rotShPre_subst_common_ty w hws3 T QO QN hPair hParts.1)
        (rotShPre_subst_common_dtc w hws3 c QO QN hPair hParts.2)

private theorem rotShPre_subst_common_dt {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false) :
    ∀ (d : SmtDatatype) (QO QN : SmtDatatype),
      RotShPreDt s3 dead QO QN →
      preCascPairDt s3 w dead QO QN d d = true →
      RotShPreDt s3 dead (__smtx_dt_substitute w QO d)
        (__smtx_dt_substitute w QN d)
  | SmtDatatype.null, QO, QN, _, _ => by
      rw [show __smtx_dt_substitute w QO SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotShPreDt.null
  | SmtDatatype.sum c d, QO, QN, hPair, hCasc => by
      have hParts := preCascPairDt_parts hCasc
      rw [show __smtx_dt_substitute w QO (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute w QO c)
            (__smtx_dt_substitute w QO d) by simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN (SmtDatatype.sum c d) =
          SmtDatatype.sum (__smtx_dtc_substitute w QN c)
            (__smtx_dt_substitute w QN d) by simp [__smtx_dt_substitute]]
      exact RotShPreDt.sum
        (rotShPre_subst_common_dtc w hws3 c QO QN hPair hParts.1)
        (rotShPre_subst_common_dt w hws3 d QO QN hPair hParts.2)

end

mutual

private theorem rotShPre_subst_pair_ty {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false)
    (hwlive : dead w = false) :
    ∀ {TO TN : SmtType} (QO QN : SmtDatatype),
      RotShPreTy s3 dead TO TN → RotShPreDt s3 dead QO QN →
      preCascPairTy s3 w dead QO QN TO TN = true →
      RotShPreTy s3 dead (__smtx_type_substitute w QO TO)
        (__smtx_type_substitute w QN TN)
  | _, _, QO, QN, RotShPreTy.same T, hPair, hCasc =>
      rotShPre_subst_common_ty w hws3 T QO QN hPair hCasc
  | _, _, QO, QN, @RotShPreTy.dt _ _ q ZO ZN hq hBody, hPair, hCasc => by
      cases hwq : native_streq w q with
      | true =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q ZO) =
              SmtType.Datatype q ZO by
            simp [__smtx_type_substitute, native_ite, hwq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q ZN) =
              SmtType.Datatype q ZN by
            simp [__smtx_type_substitute, native_ite, hwq]]
          exact RotShPreTy.dt hq hBody
      | false =>
          rw [show __smtx_type_substitute w QO (SmtType.Datatype q ZO) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q ZO QO) ZO) by
            simp [__smtx_type_substitute, native_ite, hwq]]
          rw [show __smtx_type_substitute w QN (SmtType.Datatype q ZN) =
              SmtType.Datatype q
                (__smtx_dt_substitute w (__smtx_dt_lift q ZN QN) ZN) by
            simp [__smtx_type_substitute, native_ite, hwq]]
          have hParts := preCascPairTy_parts hwq hq hCasc
          exact RotShPreTy.dt hq
            (rotShPre_subst_pair_dt w hws3 hwlive
              (__smtx_dt_lift q ZO QO) (__smtx_dt_lift q ZN QN) hBody
              (rotShPre_lift_pair_dt q ZO ZN hParts.1 hq hPair
                hParts.2.1)
              hParts.2.2)
  | _, _, QO, QN, @RotShPreTy.rotAny _ _ ZO ZN, hPair, _ => by
      have hs3w : native_streq w s3 = false := hws3
      rw [show __smtx_type_substitute w QO (SmtType.Datatype s3 ZO) =
          SmtType.Datatype s3
            (__smtx_dt_substitute w (__smtx_dt_lift s3 ZO QO) ZO) by
        simp [__smtx_type_substitute, native_ite, hs3w]]
      rw [show __smtx_type_substitute w QN (SmtType.Datatype s3 ZN) =
          SmtType.Datatype s3
            (__smtx_dt_substitute w (__smtx_dt_lift s3 ZN QN) ZN) by
        simp [__smtx_type_substitute, native_ite, hs3w]]
      exact RotShPreTy.rotAny
  | _, _, QO, QN, @RotShPreTy.preRot _ _ ZO, hPair, _ => by
      rw [show __smtx_type_substitute w QO (SmtType.Datatype s3 ZO) =
          SmtType.Datatype s3
            (__smtx_dt_substitute w (__smtx_dt_lift s3 ZO QO) ZO) by
        simp [__smtx_type_substitute, native_ite, hws3]]
      rw [show __smtx_type_substitute w QN (SmtType.TypeRef s3) =
          SmtType.TypeRef s3 by
        simp [__smtx_type_substitute, native_ite, hws3]]
      exact RotShPreTy.preRot
  | _, _, QO, QN, @RotShPreTy.flip _ _ r TN hr, hPair, _ => by
      have hwr : native_streq w r = false := by
        cases hT : native_streq w r with
        | false => rfl
        | true =>
            have hEq : w = r := by simpa [native_streq] using hT
            rw [hEq, hr] at hwlive
            cases hwlive
      rw [show __smtx_type_substitute w QO (SmtType.TypeRef r) =
          SmtType.TypeRef r by
        simp [__smtx_type_substitute, native_ite, hwr]]
      exact RotShPreTy.flip hr

private theorem rotShPre_subst_pair_dtc {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false)
    (hwlive : dead w = false) :
    ∀ {cO cN : SmtDatatypeCons} (QO QN : SmtDatatype),
      RotShPreDtc s3 dead cO cN → RotShPreDt s3 dead QO QN →
      preCascPairDtc s3 w dead QO QN cO cN = true →
      RotShPreDtc s3 dead (__smtx_dtc_substitute w QO cO)
        (__smtx_dtc_substitute w QN cN)
  | _, _, QO, QN, RotShPreDtc.unit, _, _ => by
      rw [show __smtx_dtc_substitute w QO SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN SmtDatatypeCons.unit =
          SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact RotShPreDtc.unit
  | _, _, QO, QN, @RotShPreDtc.cons _ _ TO TN cO cN hT hc, hPair,
      hCasc => by
      have hParts := preCascPairDtc_parts hCasc
      rw [show __smtx_dtc_substitute w QO (SmtDatatypeCons.cons TO cO) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QO TO)
            (__smtx_dtc_substitute w QO cO) by
        simp [__smtx_dtc_substitute]]
      rw [show __smtx_dtc_substitute w QN (SmtDatatypeCons.cons TN cN) =
          SmtDatatypeCons.cons (__smtx_type_substitute w QN TN)
            (__smtx_dtc_substitute w QN cN) by
        simp [__smtx_dtc_substitute]]
      exact RotShPreDtc.cons
        (rotShPre_subst_pair_ty w hws3 hwlive QO QN hT hPair hParts.1)
        (rotShPre_subst_pair_dtc w hws3 hwlive QO QN hc hPair hParts.2)

private theorem rotShPre_subst_pair_dt {s3 : native_String}
    {dead : native_String → native_Bool}
    (w : native_String) (hws3 : native_streq w s3 = false)
    (hwlive : dead w = false) :
    ∀ {dO dN : SmtDatatype} (QO QN : SmtDatatype),
      RotShPreDt s3 dead dO dN → RotShPreDt s3 dead QO QN →
      preCascPairDt s3 w dead QO QN dO dN = true →
      RotShPreDt s3 dead (__smtx_dt_substitute w QO dO)
        (__smtx_dt_substitute w QN dN)
  | _, _, QO, QN, RotShPreDt.null, _, _ => by
      rw [show __smtx_dt_substitute w QO SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN SmtDatatype.null =
          SmtDatatype.null by simp [__smtx_dt_substitute]]
      exact RotShPreDt.null
  | _, _, QO, QN, @RotShPreDt.sum _ _ cO cN dO dN hc hd, hPair,
      hCasc => by
      have hParts := preCascPairDt_parts hCasc
      rw [show __smtx_dt_substitute w QO (SmtDatatype.sum cO dO) =
          SmtDatatype.sum (__smtx_dtc_substitute w QO cO)
            (__smtx_dt_substitute w QO dO) by
        simp [__smtx_dt_substitute]]
      rw [show __smtx_dt_substitute w QN (SmtDatatype.sum cN dN) =
          SmtDatatype.sum (__smtx_dtc_substitute w QN cN)
            (__smtx_dt_substitute w QN dN) by
        simp [__smtx_dt_substitute]]
      exact RotShPreDt.sum
        (rotShPre_subst_pair_dtc w hws3 hwlive QO QN hc hPair hParts.1)
        (rotShPre_subst_pair_dt w hws3 hwlive QO QN hd hPair hParts.2)

end

/-! ### The chain iteration

Pre-refill rotation is monotone in the dead set (only `flip` consults
it), so a whole aligned chain of paired steps preserves it: each step
runs under its own dead set — in which its entry name is still live —
and afterwards the name joins the dead set for the remaining steps. -/

mutual

private theorem rotShPre_mono_ty {s3 : native_String}
    {dead dead' : native_String → native_Bool}
    (hMono : ∀ r, dead r = true → dead' r = true) :
    ∀ {TO TN : SmtType}, RotShPreTy s3 dead TO TN →
      RotShPreTy s3 dead' TO TN
  | _, _, RotShPreTy.same T => RotShPreTy.same T
  | _, _, RotShPreTy.dt hq hBody =>
      RotShPreTy.dt hq (rotShPre_mono_dt hMono hBody)
  | _, _, RotShPreTy.rotAny => RotShPreTy.rotAny
  | _, _, RotShPreTy.preRot => RotShPreTy.preRot
  | _, _, RotShPreTy.flip hr => RotShPreTy.flip (hMono _ hr)

private theorem rotShPre_mono_dtc {s3 : native_String}
    {dead dead' : native_String → native_Bool}
    (hMono : ∀ r, dead r = true → dead' r = true) :
    ∀ {cO cN : SmtDatatypeCons}, RotShPreDtc s3 dead cO cN →
      RotShPreDtc s3 dead' cO cN
  | _, _, RotShPreDtc.unit => RotShPreDtc.unit
  | _, _, RotShPreDtc.cons hT hc =>
      RotShPreDtc.cons (rotShPre_mono_ty hMono hT)
        (rotShPre_mono_dtc hMono hc)

private theorem rotShPre_mono_dt {s3 : native_String}
    {dead dead' : native_String → native_Bool}
    (hMono : ∀ r, dead r = true → dead' r = true) :
    ∀ {dO dN : SmtDatatype}, RotShPreDt s3 dead dO dN →
      RotShPreDt s3 dead' dO dN
  | _, _, RotShPreDt.null => RotShPreDt.null
  | _, _, RotShPreDt.sum hc hd =>
      RotShPreDt.sum (rotShPre_mono_dtc hMono hc)
        (rotShPre_mono_dt hMono hd)

end

/-- The dead set after processing an entry: its name is dead thereafter. -/
private def deadAfter (dead : native_String → native_Bool)
    (w : native_String) : native_String → native_Bool :=
  fun r => native_or (dead r) (native_streq r w)

private theorem deadAfter_mono (dead : native_String → native_Bool)
    (w : native_String) :
    ∀ r, dead r = true → deadAfter dead w r = true := by
  intro r h
  simp [deadAfter, native_or, h]

private abbrev PairSteps :=
  List (native_String × SmtDatatype × SmtDatatype)

private def pairApplyO : PairSteps → SmtDatatype → SmtDatatype
  | [], A => A
  | (w, QO, _) :: rest, A =>
      pairApplyO rest (__smtx_dt_substitute w QO A)

private def pairApplyN : PairSteps → SmtDatatype → SmtDatatype
  | [], A => A
  | (w, _, QN) :: rest, A =>
      pairApplyN rest (__smtx_dt_substitute w QN A)

private def deadFold :
    (native_String → native_Bool) → PairSteps →
    (native_String → native_Bool)
  | dead, [] => dead
  | dead, (w, _, _) :: rest => deadFold (deadAfter dead w) rest

/-- Per-step premises of an aligned chain of paired substitutions: each
entry name avoids `s3`, is live in its step's dead set, its payloads are
pre-refill rotated, and the fold-alignment cascade holds against the
current accumulators. -/
private inductive ChainPairOK (s3 : native_String) :
    (native_String → native_Bool) → PairSteps →
    SmtDatatype → SmtDatatype → Prop where
  | nil {dead : native_String → native_Bool} {AO AN : SmtDatatype} :
      ChainPairOK s3 dead [] AO AN
  | cons {dead : native_String → native_Bool} {w : native_String}
      {QO QN : SmtDatatype} {rest : PairSteps} {AO AN : SmtDatatype} :
      native_streq w s3 = false →
      dead w = false →
      RotShPreDt s3 dead QO QN →
      preCascPairDt s3 w dead QO QN AO AN = true →
      ChainPairOK s3 (deadAfter dead w) rest
        (__smtx_dt_substitute w QO AO) (__smtx_dt_substitute w QN AN) →
      ChainPairOK s3 dead ((w, QO, QN) :: rest) AO AN

/-- An aligned chain of paired substitutions preserves pre-refill
rotation, with the dead set folding over the processed entry names. -/
private theorem rotShPre_chain {s3 : native_String} :
    ∀ (steps : PairSteps) (dead : native_String → native_Bool)
      (AO AN : SmtDatatype),
      RotShPreDt s3 dead AO AN →
      ChainPairOK s3 dead steps AO AN →
      RotShPreDt s3 (deadFold dead steps)
        (pairApplyO steps AO) (pairApplyN steps AN)
  | [], dead, AO, AN, hRel, _ => by
      simpa [pairApplyO, pairApplyN, deadFold] using hRel
  | (w, QO, QN) :: rest, dead, AO, AN, hRel, hOK => by
      cases hOK with
      | cons hws3 hwlive hPair hCasc hRest =>
          have hStep := rotShPre_subst_pair_dt w hws3 hwlive QO QN
            hRel hPair hCasc
          have hStep' := rotShPre_mono_dt (deadAfter_mono dead w) hStep
          simpa [pairApplyO, pairApplyN, deadFold] using
            rotShPre_chain rest (deadAfter dead w) _ _ hStep' hRest

/-- Chains act compositionally: appended entries substitute afterwards. -/
private theorem chain_ty_append :
    ∀ (σ τ : SubstChain) (T : SmtType),
      chain_ty (σ ++ τ) T = chain_ty τ (chain_ty σ T)
  | [], _, _ => rfl
  | (s, _R, P) :: σ, τ, T => by
      simp only [List.cons_append, chain_ty]
      exact chain_ty_append σ τ (__smtx_type_substitute s P T)

/-- Closed form of the re-resolved head after a descent: the resolution
under the *descended* chain, with the closed node body — lifted under the
head binder — substituted for `s3`.  This is the algebraic backbone for
establishing the rotation certificate: the entire difference between the
old and new resolutions is one `s3`-substitution against the descended
resolution. -/
private theorem selfExt_resolution
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (hne : native_streq s3 t = false)
    (DD : SmtDatatype)
    (hDD : chain_ty (chain_descend ρ s3 X) (SmtType.TypeRef t) =
      SmtType.Datatype t DD) :
    chain_ty (selfExt ρ s3 X) (SmtType.TypeRef t) =
      SmtType.Datatype t
        (__smtx_dt_substitute s3
          (__smtx_dt_lift t DD (chain_dt (chain_descend ρ s3 X) X)) DD) := by
  rw [selfExt, chain_ty_append, hDD]
  simp [chain_ty, __smtx_type_substitute, native_ite, hne]

/-
There is one further, essential restriction on "valid raw histories".  The
statement below was false with the *original* `ChainSourceOK`, which only
reconstructed the head payload while `RawSuffixCons` deliberately ignored
every suffix payload.  Here is the exact counterexample (constructor lists
are written as lists of field lists):

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
well-formed against itself).  `ChainSourceOK` has since gained payload
provenance (`ChainOriginAcc`): the bad `Q` is not a scoped image of its raw
body `U` (the nested body has one constructor where `X` has two), so this
counterexample no longer satisfies the hypotheses.

The remaining hole is the establishment of the rotation certificate below:
`RotAllDt s3 P' (subst t D D) (subst t D' D')` for the old resolved head `D`
and the re-resolved head `D'`.  Machine sweeps (see the rotation-transport
section) confirm the certificate holds at every reachable descent event:
the two resolutions differ only inside `s3`-named nodes, the per-spot
inhabitedness implications hold, and both facts persist under the diagonal
re-rootings demanded by the certificate.  The corresponding closed-form
identity `D' = subst s3 (lift t DD B) DD` — with `DD` the resolution under
the descended chain and `B` the newly closed node body — also checks on
every reachable event and is the intended backbone of the establishment
proof, which must thread the per-spot implications from `hInhNode` through
the lift stack of the refill.
-/
private theorem chainok_selfExt_facts
    (ρ : SubstChain) (s3 : native_String) (X : SmtDatatype)
    (t : native_String) (R P : SmtDatatype) (REST : SubstChain)
    (hρ : ρ = (t, R, P) :: REST)
    (hne : native_streq t s3 = false)
    (hFresh : chainHasName s3 REST = false)
    (hField : __smtx_type_names_consistent_rec R
      (SmtType.Datatype s3 X) = true)
    (hEmbed : RootEmbeddedTy R (SmtType.Datatype s3 X))
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
  have hD : D = chain_dt (chain_descend REST t P) P := by
    have hCanonical := hRes
    rw [show
        chain_ty ((t, R, P) :: REST) (SmtType.TypeRef t) =
          chain_ty REST (SmtType.Datatype t P) by
        simp [chain_ty, __smtx_type_substitute, native_ite, native_streq]]
      at hCanonical
    rw [chain_ty_datatype] at hCanonical
    injection hCanonical with _hName hBody
    exact hBody.symm
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
  let P' := __smtx_dt_lift s3 X P
  let REST' :=
    chain_descend REST s3 (__smtx_dt_substitute t P' X) ++
      [(s3, X, chain_dt (chain_descend ((t, R, P) :: REST) s3 X) X)]
  have hSource' : ChainSourceOK t R P' REST' := by
    exact ChainSourceOK_descend t s3 R P X
      (__smtx_dt_substitute t (__smtx_dt_lift s3 X P) X)
      REST hSource hne hFresh hField hEmbed
  rw [hSelfExt]
  change ChainOK ((t, R, P') :: REST')
  refine chainok_head_facts t R P' REST' ?_ hSource'
  constructor
  · exact inhabited_of_img _ t R _
      (chainSource_head_img t R P' REST' hSource') hSource'.2.2.1
  · have hOldLift :
        __smtx_dt_wf_rec (__smtx_dt_substitute t D D) P' = true := by
      exact guideTrDt_wf (lift_guide_tr_dt s3 X hSkel) hWf
    -- context facts for the certificate assembly: the new guide has no
    -- `s3`-named nodes, and both diagonals are FSkel-aligned to it
    have hGuideNoS3 : noDtDt s3 P' = true :=
      noDt_lift_of_noStray_dt s3 X P hNoStrayP
    have hSkelO : FSkelDt (__smtx_dt_substitute t D D) P' :=
      fskel_lift_dt s3 X hSkel
    have hSkelN :
        FSkelDt
          (__smtx_dt_substitute t (chain_dt (chain_descend REST' t P') P')
            (chain_dt (chain_descend REST' t P') P')) P' := by
      have h := fskel_master_dt P'
        (chain_descend REST' t P' ++
          [(t, R, chain_dt (chain_descend REST' t P') P')])
      rwa [chain_dt_append_one] at h
    apply foldObsDt_wf (hOld := hOldLift)
    apply rotAllDt_foldObs (s3 := s3)
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
    (hEmbed : RootEmbeddedTy R (SmtType.Datatype s3 X))
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
        REST hSource hne hFresh hField hEmbed
  · exact chainok_selfExt_facts ρ s3 X t R P REST hρ hne hFresh hField
      hEmbed hNoNames hOK hInhNode hWfNode hUse hStable

/-! The establishment walk: over a raw guide `dU`, the image under a chain
with head `(t, P)` transports the guide from `dU` to `dt_substitute t P dU`,
given the chain invariant and the old well-formedness (whose pattern-2 facts
feed the chain-invariant maintenance at nested descents). -/
mutual

private theorem estab_ty :
    ∀ (TU : SmtType) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_type_names_consistent_rec R TU = true →
      RootEmbeddedTy R TU →
      LocalNoSelfTy TU = true →
      ChainNoDtTy REST TU →
      (usesHeadTy t TU = true → ChainOK ((t, R, P) :: REST)) →
      (∀ (s3 : native_String) (X : SmtDatatype), TU = SmtType.Datatype s3 X →
        native_inhabited_type (chain_ty ((t, R, P) :: REST) TU) = true ∧
          __smtx_type_wf_rec (chain_ty ((t, R, P) :: REST) TU) TU = true) →
      GuideTr (chain_ty ((t, R, P) :: REST) TU) TU
        (__smtx_type_substitute t P TU)
  | SmtType.TypeRef r, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
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
  | SmtType.Datatype s3 X, t, R, P, REST, hCons, hEmb, hLocal, hNoDt,
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
              rfl hs hNoDtParts.1 hCons hEmb hNoDtParts.2 hOK hInhNode hWfNode hUse
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
            hConsParts.2 (RootEmbeddedTy_body R s3 X hEmb) hLocalParts.2
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
  | SmtType.None, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.None = SmtType.None by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Bool, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Bool = SmtType.Bool by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Int, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Int = SmtType.Int by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Real, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Real = SmtType.Real by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.RegLan, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.RegLan = SmtType.RegLan by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.BitVec w, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.BitVec w) = SmtType.BitVec w by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Map A B, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Map A B) = SmtType.Map A B by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Set A, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Set A) = SmtType.Set A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Seq A, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.Seq A) = SmtType.Seq A by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.Char, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P SmtType.Char = SmtType.Char by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.USort u, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.USort u) = SmtType.USort u by
          simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.FunType A B, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.FunType A B) =
          SmtType.FunType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _
  | SmtType.DtcAppType A B, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOldField => by
      rw [chain_ty_fix _ (by intro s Q; simp [__smtx_type_substitute]) _,
        show __smtx_type_substitute t P (SmtType.DtcAppType A B) =
          SmtType.DtcAppType A B by simp [__smtx_type_substitute]]
      exact GuideTr.same _ _

private theorem estab_dtc :
    ∀ (cU : SmtDatatypeCons) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_dt_cons_names_consistent_rec R cU = true →
      RootEmbeddedDtc R cU →
      LocalNoSelfDtc cU = true →
      ChainNoDtDtc REST cU →
      (usesHeadDtc t cU = true → ChainOK ((t, R, P) :: REST)) →
      __smtx_dt_cons_wf_rec (chain_dtc ((t, R, P) :: REST) cU) cU = true →
      GuideTrDtc (chain_dtc ((t, R, P) :: REST) cU) cU
        (__smtx_dtc_substitute t P cU)
  | SmtDatatypeCons.unit, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOld => by
      rw [chain_dtc_unit]
      rw [show __smtx_dtc_substitute t P SmtDatatypeCons.unit =
        SmtDatatypeCons.unit by simp [__smtx_dtc_substitute]]
      exact GuideTrDtc.unit
  | SmtDatatypeCons.cons TU cU, t, R, P, REST, hCons, hEmb, hLocal, hNoDt,
      hNeed, hOld => by
      have hConsParts := namesConsDtc_parts R TU cU hCons
      have hEmbParts := RootEmbeddedDtc_parts R TU cU hEmb
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
        (estab_ty TU t R P REST hConsParts.1 hEmbParts.1 hLocalParts.1 hNoDtParts.1
          hNeedHead hOldField)
        (estab_dtc cU t R P REST hConsParts.2 hEmbParts.2 hLocalParts.2 hNoDtParts.2
          hNeedTail hTail)

private theorem estab_dt :
    ∀ (dU : SmtDatatype) (t : native_String) (R P : SmtDatatype)
      (REST : SubstChain),
      __smtx_dt_names_consistent_rec R dU = true →
      RootEmbeddedDt R dU →
      LocalNoSelfDt dU = true →
      ChainNoDtDt REST dU →
      (usesHeadDt t dU = true → ChainOK ((t, R, P) :: REST)) →
      __smtx_dt_wf_rec (chain_dt ((t, R, P) :: REST) dU) dU = true →
      GuideTrDt (chain_dt ((t, R, P) :: REST) dU) dU
        (__smtx_dt_substitute t P dU)
  | SmtDatatype.null, t, R, P, REST, _hCons, _hEmb, _hLocal, _hNoDt,
      _hOK, _hOld => by
      rw [chain_dt_null]
      rw [show __smtx_dt_substitute t P SmtDatatype.null = SmtDatatype.null by
        simp [__smtx_dt_substitute]]
      exact GuideTrDt.null
  | SmtDatatype.sum cU dU, t, R, P, REST, hCons, hEmb, hLocal, hNoDt,
      hNeed, hOld => by
      have hConsParts := namesConsDt_parts R cU dU hCons
      have hEmbParts := RootEmbeddedDt_parts R cU dU hEmb
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
        (estab_dtc cU t R P REST hConsParts.1 hEmbParts.1 hLocalParts.1 hNoDtParts.1
          hNeedHead hParts.1)
        (estab_dt dU t R P REST hConsParts.2 hEmbParts.2 hLocalParts.2 hNoDtParts.2
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
    (hFieldEmb : RootEmbeddedTy dP (SmtType.Datatype sC dC))
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
    · exact ⟨rfl, hPNC, hPInh, trivial, trivial,
        ⟨by simpa [ChainOriginAcc, rawFolds] using
          ctxImg_refl_dt [] native_reflist_nil dP, trivial⟩,
        ⟨rfl, trivial⟩⟩
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
      rfl hne rfl hFieldNC hFieldEmb trivial hOK0
      (by rw [hNode0]; exact hInhBC) (by rw [hNode0]; exact hOld) hUse
  have hFold0 :
      chain_dt [(sP, dP, __smtx_dt_lift sC dC dP), (sC, dC, BC)] dC =
        __smtx_dt_substitute sC BC BC := by
    simp [chain_dt, hBC]
  have hFieldParts := namesConsTy_parts dP sC dC hFieldNC
  have hWalk := estab_dt dC sP dP (__smtx_dt_lift sC dC dP)
    [(sC, dC, BC)] hFieldParts.2
    (RootEmbeddedTy_body dP sC dC hFieldEmb) hCLocal
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
    (hFieldEmb : RootEmbeddedTy dP (SmtType.Datatype sC dC))
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
        hFieldNC hFieldEmb hCNoSelf hCLocal
        (__smtx_dt_substitute sP (__smtx_dt_lift sC dC dP) dC) rfl hFInh hOld
      simpa [__smtx_type_wf_rec] using guideTrDt_wf hTr hOld

end Smtm
