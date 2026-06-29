import Cpc.Proofs.Canonical.FiniteDefaultable
open SmtEval Smtm
namespace Smtm
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# Infinite datatype pump — foundation (free-reference tracking + substitution facts)

Step 1 of porting the "pump" that builds arbitrarily-large canonical inhabitants of an
infinite well-formed datatype.  Ported from the pre-`dtMutual` development; the new
`__smtx_dt_lift` folding (added by the refactor) required a fresh `*_lift_unref` theory,
and the dropped `native_inhabited_type` gate in `__smtx_dt_cons_wf_rec` required dropping
the now-absent inhabited conjunct in the wf-extraction lemmas.
-/

private theorem dt_cons_wf_rec_tail_of_true {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  all_goals first | exact h | exact h.2 | exact h.2.2

private theorem dt_wf_cons_of_wf {c : SmtDatatypeCons} {d : SmtDatatype} {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  by_cases hc : __smtx_dt_cons_wf_rec c refs = true
  · exact hc
  · have hF : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = false := by
      cases d <;> simp [__smtx_dt_wf_rec, native_ite, hc]
    rw [hF] at h; simp at h

private theorem dt_wf_tail_of_nonempty_tail_wf {c cTail : SmtDatatypeCons} {dTail : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true := dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

mutual

private def smt_type_unref (s : native_String) : SmtType -> Bool
  | SmtType.TypeRef r => native_not (native_streq s r)
  | SmtType.Datatype s2 d2 =>
      native_ite (native_streq s s2) true (smt_dt_unref s d2)
  | _ => true

private def smt_dtc_unref (s : native_String) : SmtDatatypeCons -> Bool
  | SmtDatatypeCons.unit => true
  | SmtDatatypeCons.cons T c =>
      native_and (smt_type_unref s T) (smt_dtc_unref s c)

private def smt_dt_unref (s : native_String) : SmtDatatype -> Bool
  | SmtDatatype.null => true
  | SmtDatatype.sum c d =>
      native_and (smt_dtc_unref s c) (smt_dt_unref s d)

end

-- lift preserves t-unref for names t distinct from the folded name (new `__smtx_dt_lift` theory)
mutual
private theorem type_lift_unref (t s2 : native_String) (d2 : SmtDatatype)
    (hne : native_streq t s2 = false) :
    ∀ T : SmtType, smt_type_unref t T = true → smt_type_unref t (__smtx_type_lift s2 d2 T) = true
  | SmtType.Datatype s' d', h => by
      simp only [__smtx_type_lift]
      by_cases hT : native_Teq (SmtType.Datatype s2 d2) (SmtType.Datatype s' d') = true
      · rw [native_ite, if_pos hT]; simp [smt_type_unref, native_not, hne]
      · rw [native_ite, if_neg hT]
        by_cases hs' : native_streq t s' = true
        · simp [smt_type_unref, native_ite, hs']
        · have hd' : smt_dt_unref t d' = true := by
            simpa [smt_type_unref, native_ite, hs'] using h
          simp [smt_type_unref, native_ite, hs', dt_lift_unref t s2 d2 hne d' hd']
  | SmtType.TypeRef r, h => by simpa [__smtx_type_lift] using h
  | SmtType.None, h => by simpa [__smtx_type_lift] using h
  | SmtType.Bool, h => by simpa [__smtx_type_lift] using h
  | SmtType.Int, h => by simpa [__smtx_type_lift] using h
  | SmtType.Real, h => by simpa [__smtx_type_lift] using h
  | SmtType.RegLan, h => by simpa [__smtx_type_lift] using h
  | SmtType.BitVec w, h => by simpa [__smtx_type_lift] using h
  | SmtType.Map A B, h => by simpa [__smtx_type_lift] using h
  | SmtType.Set A, h => by simpa [__smtx_type_lift] using h
  | SmtType.Seq A, h => by simpa [__smtx_type_lift] using h
  | SmtType.Char, h => by simpa [__smtx_type_lift] using h
  | SmtType.USort i, h => by simpa [__smtx_type_lift] using h
  | SmtType.FunType A B, h => by simpa [__smtx_type_lift] using h
  | SmtType.DtcAppType A B, h => by simpa [__smtx_type_lift] using h
private theorem dtc_lift_unref (t s2 : native_String) (d2 : SmtDatatype)
    (hne : native_streq t s2 = false) :
    ∀ c : SmtDatatypeCons, smt_dtc_unref t c = true → smt_dtc_unref t (__smtx_dtc_lift s2 d2 c) = true
  | SmtDatatypeCons.unit, h => by simpa [__smtx_dtc_lift] using h
  | SmtDatatypeCons.cons T c, h => by
      have hp : smt_type_unref t T = true ∧ smt_dtc_unref t c = true := by
        simpa [smt_dtc_unref, native_and] using h
      simp [__smtx_dtc_lift, smt_dtc_unref, native_and,
        type_lift_unref t s2 d2 hne T hp.1, dtc_lift_unref t s2 d2 hne c hp.2]
private theorem dt_lift_unref (t s2 : native_String) (d2 : SmtDatatype)
    (hne : native_streq t s2 = false) :
    ∀ d0 : SmtDatatype, smt_dt_unref t d0 = true → smt_dt_unref t (__smtx_dt_lift s2 d2 d0) = true
  | SmtDatatype.null, h => by simpa [__smtx_dt_lift] using h
  | SmtDatatype.sum c d0, h => by
      have hp : smt_dtc_unref t c = true ∧ smt_dt_unref t d0 = true := by
        simpa [smt_dt_unref, native_and] using h
      simp [__smtx_dt_lift, smt_dt_unref, native_and,
        dtc_lift_unref t s2 d2 hne c hp.1, dt_lift_unref t s2 d2 hne d0 hp.2]
end

mutual

private theorem type_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType,
      smt_type_unref s T = true -> __smtx_type_substitute s d T = T
  | SmtType.TypeRef r, h => by
      have hr : native_streq s r = false := by
        cases hsr : native_streq s r <;>
          simp [smt_type_unref, native_not, hsr] at h ⊢
      simp [__smtx_type_substitute, native_ite, hr]
  | SmtType.Datatype s2 d2, h => by
      cases hs : native_streq s s2 with
      | true =>
          simp [__smtx_type_substitute, native_ite, hs]
      | false =>
          have h2 : smt_dt_unref s d2 = true := by
            simpa [smt_type_unref, native_ite, hs] using h
          simp [__smtx_type_substitute, native_ite, hs,
            dt_substitute_eq_self_of_unref s (__smtx_dt_lift s2 d2 d) d2 h2]
  | SmtType.None, _ => by simp [__smtx_type_substitute]
  | SmtType.Bool, _ => by simp [__smtx_type_substitute]
  | SmtType.Int, _ => by simp [__smtx_type_substitute]
  | SmtType.Real, _ => by simp [__smtx_type_substitute]
  | SmtType.RegLan, _ => by simp [__smtx_type_substitute]
  | SmtType.BitVec _, _ => by simp [__smtx_type_substitute]
  | SmtType.Map _ _, _ => by simp [__smtx_type_substitute]
  | SmtType.Set _, _ => by simp [__smtx_type_substitute]
  | SmtType.Seq _, _ => by simp [__smtx_type_substitute]
  | SmtType.Char, _ => by simp [__smtx_type_substitute]
  | SmtType.USort _, _ => by simp [__smtx_type_substitute]
  | SmtType.FunType _ _, _ => by simp [__smtx_type_substitute]
  | SmtType.DtcAppType _ _, _ => by simp [__smtx_type_substitute]

private theorem dtc_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref s c = true -> __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _ => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, h => by
      have hParts : smt_type_unref s T = true ∧ smt_dtc_unref s c = true := by
        simpa [smt_dtc_unref, native_and] using h
      simp [__smtx_dtc_substitute,
        type_substitute_eq_self_of_unref s d T hParts.1,
        dtc_substitute_eq_self_of_unref s d c hParts.2]

private theorem dt_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref s d0 = true -> __smtx_dt_substitute s d d0 = d0
  | SmtDatatype.null, _ => by
      simp [__smtx_dt_substitute]
  | SmtDatatype.sum c d0, h => by
      have hParts : smt_dtc_unref s c = true ∧ smt_dt_unref s d0 = true := by
        simpa [smt_dt_unref, native_and] using h
      simp [__smtx_dt_substitute,
        dtc_substitute_eq_self_of_unref s d c hParts.1,
        dt_substitute_eq_self_of_unref s d d0 hParts.2]

end

mutual

private theorem type_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType, smt_type_unref s (__smtx_type_substitute s d T) = true
  | SmtType.TypeRef r => by
      cases hr : native_streq s r with
      | true =>
          have hsr : s = r := by simpa [native_streq] using hr
          subst hsr
          simp [__smtx_type_substitute, native_ite, smt_type_unref,
            native_streq]
      | false =>
          simp [__smtx_type_substitute, native_ite, hr, smt_type_unref,
            native_not]
  | SmtType.Datatype s2 d2 => by
      cases hs : native_streq s s2 with
      | true =>
          simp [__smtx_type_substitute, native_ite, hs, smt_type_unref]
      | false =>
          simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
            dt_unref_substitute_self s (__smtx_dt_lift s2 d2 d) d2]
  | SmtType.None => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Bool => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Int => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Real => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.RegLan => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.BitVec _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Map _ _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Set _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Seq _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Char => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.USort _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.FunType _ _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.DtcAppType _ _ => by
      simp [__smtx_type_substitute, smt_type_unref]

private theorem dtc_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref s (__smtx_dtc_substitute s d c) = true
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_substitute, smt_dtc_unref]
  | SmtDatatypeCons.cons T c => by
      simp [__smtx_dtc_substitute, smt_dtc_unref, native_and,
        type_unref_substitute_self s d T,
        dtc_unref_substitute_self s d c]

private theorem dt_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref s (__smtx_dt_substitute s d d0) = true
  | SmtDatatype.null => by
      simp [__smtx_dt_substitute, smt_dt_unref]
  | SmtDatatype.sum c d0 => by
      simp [__smtx_dt_substitute, smt_dt_unref, native_and,
        dtc_unref_substitute_self s d c,
        dt_unref_substitute_self s d d0]

end

mutual

private theorem type_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ T : SmtType,
      smt_type_unref t T = true ->
        smt_type_unref t (__smtx_type_substitute s d T) = true
  | SmtType.TypeRef r, h => by
      cases hr : native_streq s r with
      | true =>
          cases hts : native_streq t s <;>
            simp [__smtx_type_substitute, native_ite, hr, smt_type_unref,
              hts, hd]
      | false =>
          simpa [__smtx_type_substitute, native_ite, hr] using h
  | SmtType.Datatype s2 d2, h => by
      cases hs : native_streq s s2 with
      | true =>
          simpa [__smtx_type_substitute, native_ite, hs] using h
      | false =>
          cases hts : native_streq t s2 with
          | true =>
              simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
                hts]
          | false =>
              have h2 : smt_dt_unref t d2 = true := by
                simpa [smt_type_unref, native_ite, hts] using h
              simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
                hts, dt_unref_substitute_other s (__smtx_dt_lift s2 d2 d) t (dt_lift_unref t s2 d2 hts d hd) d2 h2]
  | SmtType.None, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Bool, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Int, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Real, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.RegLan, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.BitVec _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Map _ _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Set _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Seq _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Char, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.USort _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.FunType _ _, _ => by
      simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.DtcAppType _ _, _ => by
      simp [__smtx_type_substitute, smt_type_unref]

private theorem dtc_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref t c = true ->
        smt_dtc_unref t (__smtx_dtc_substitute s d c) = true
  | SmtDatatypeCons.unit, _ => by
      simp [__smtx_dtc_substitute, smt_dtc_unref]
  | SmtDatatypeCons.cons T c, h => by
      have hParts : smt_type_unref t T = true ∧ smt_dtc_unref t c = true := by
        simpa [smt_dtc_unref, native_and] using h
      simp [__smtx_dtc_substitute, smt_dtc_unref, native_and,
        type_unref_substitute_other s d t hd T hParts.1,
        dtc_unref_substitute_other s d t hd c hParts.2]

private theorem dt_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref t d0 = true ->
        smt_dt_unref t (__smtx_dt_substitute s d d0) = true
  | SmtDatatype.null, _ => by
      simp [__smtx_dt_substitute, smt_dt_unref]
  | SmtDatatype.sum c d0, h => by
      have hParts : smt_dtc_unref t c = true ∧ smt_dt_unref t d0 = true := by
        simpa [smt_dt_unref, native_and] using h
      simp [__smtx_dt_substitute, smt_dt_unref, native_and,
        dtc_unref_substitute_other s d t hd c hParts.1,
        dt_unref_substitute_other s d t hd d0 hParts.2]

end

mutual

private theorem type_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (T : SmtType) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_type_wf_rec T refs = true ->
          smt_type_unref t T = true
  | SmtType.TypeRef _r, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Datatype s2 d2, refs, hNot, hWf => by
      cases hts : native_streq t s2 with
      | true =>
          simp [smt_type_unref, native_ite, hts]
      | false =>
          have hParts :
              ¬ s2 ∈ refs ∧
                __smtx_dt_wf_rec d2 (native_reflist_insert refs s2) = true := by
            simpa [__smtx_type_wf_rec, native_reflist_contains,
              native_ite] using hWf
          have hNot2 :
              native_reflist_contains (native_reflist_insert refs s2) t =
                false := by
            have hts' : t ≠ s2 := by
              intro hEq
              subst hEq
              simp [native_streq] at hts
            simp [native_reflist_contains, native_reflist_insert] at hNot ⊢
            exact ⟨hts', hNot⟩
          simp [smt_type_unref, native_ite, hts,
            dt_unref_of_wf_not_contains t d2
              (native_reflist_insert refs s2) hNot2 hParts.2]
  | SmtType.None, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Int, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Real, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.RegLan, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.BitVec _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Map _ _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Set _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Seq _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Char, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.USort _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.FunType _ _, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _ _, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf

private theorem dtc_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (c : SmtDatatypeCons) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_dt_cons_wf_rec c refs = true ->
          smt_dtc_unref t c = true
  | SmtDatatypeCons.unit, _refs, _hNot, _hWf => by
      simp [smt_dtc_unref]
  | SmtDatatypeCons.cons (SmtType.TypeRef r) c, refs, hNot, hWf => by
      have hParts :
          native_reflist_contains refs r = true ∧
            __smtx_dt_cons_wf_rec c refs = true := by
        cases hr : native_reflist_contains refs r <;>
          simp [__smtx_dt_cons_wf_rec, native_ite, hr] at hWf ⊢
        exact hWf
      have htr : native_streq t r = false := by
        cases htr : native_streq t r <;> simp [native_streq] at htr ⊢
        subst htr
        rw [hNot] at hParts
        simp at hParts
      simp [smt_dtc_unref, native_and, smt_type_unref, native_not, htr,
        dtc_unref_of_wf_not_contains t c refs hNot hParts.2]
  | SmtDatatypeCons.cons (SmtType.Datatype s2 d2) c, refs, hNot, hWf => by
      have hParts :
          __smtx_type_wf_rec (SmtType.Datatype s2 d2) refs = true ∧
              __smtx_dt_cons_wf_rec c refs = true := by
        simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
      simp [smt_dtc_unref, native_and,
        type_unref_of_wf_not_contains t (SmtType.Datatype s2 d2) refs
          hNot hParts.1,
        dtc_unref_of_wf_not_contains t c refs hNot hParts.2]
  | SmtDatatypeCons.cons SmtType.None c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons SmtType.Bool c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Int c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Real c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.RegLan c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons (SmtType.BitVec _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Map _ _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Set _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Seq _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Char c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.USort _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.FunType _ _) c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons (SmtType.DtcAppType _ _) c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf

private theorem dt_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (d0 : SmtDatatype) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_dt_wf_rec d0 refs = true ->
          smt_dt_unref t d0 = true
  | SmtDatatype.null, _refs, _hNot, hWf => by
      simp [__smtx_dt_wf_rec] at hWf
  | SmtDatatype.sum c SmtDatatype.null, refs, hNot, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      simp [smt_dt_unref, native_and,
        dtc_unref_of_wf_not_contains t c refs hNot hCons]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, hNot, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hTail :
          __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) refs = true :=
        dt_wf_tail_of_nonempty_tail_wf hWf
      have hTailUnref :=
        dt_unref_of_wf_not_contains t (SmtDatatype.sum c2 d2) refs hNot hTail
      simp [smt_dt_unref, native_and,
        dtc_unref_of_wf_not_contains t c refs hNot hCons] at hTailUnref ⊢
      exact hTailUnref

end

/--
A scope stack for nested datatype pumping, innermost level first.  Each
entry `(s, dr, D)` records a datatype level: its name `s`, its raw body
`dr` (a subterm of the original program syntax, well-formed with respect
to the names of the outer levels plus `s`), and its closed body `D`
obtained by substituting all outer levels into `dr`.
-/
private abbrev PumpEnv := List (native_String × SmtDatatype × SmtDatatype)

end Smtm
