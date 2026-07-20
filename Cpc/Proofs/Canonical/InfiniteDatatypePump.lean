module

public import Cpc.Proofs.Canonical.FiniteDefaultable
import all Cpc.Proofs.Canonical.FiniteDefaultable

public section
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

private def dt_append : SmtDatatype -> SmtDatatype -> SmtDatatype
  | SmtDatatype.null, d => d
  | SmtDatatype.sum c rest, d => SmtDatatype.sum c (dt_append rest d)

private def dt_constructor_offset : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ rest => Nat.succ (dt_constructor_offset rest)

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

/- Under the new (diagonal) `__smtx_type_wf_rec` algorithm, aliasing is permitted
   and there is no ambient reflist scope, so the old occurs-check-style derivation
   ("wf against refs => no free reference to a name outside refs") no longer holds
   in general.  Signatures are kept refs/hNot-shaped for call-site compatibility
   (the `refs` here just tracks the pump environment's already-bound names, a
   plain-data notion independent of the smt-wf algorithm), with the wf hypothesis
   changed to the diagonal self-check.  Left as `sorry` per the "rewrite from
   scratch, sorry the hard parts" directive. -/

private theorem dt_unref_of_wf_not_contains
    (t : native_String) (d0 : SmtDatatype) (refs : RefList)
    (hNot : native_reflist_contains refs t = false)
    (hWf : __smtx_dt_wf_rec d0 d0 = true) :
    smt_dt_unref t d0 = true := by
  sorry

/--
A scope stack for nested datatype pumping, innermost level first.  Each
entry `(s, dr, D)` records a datatype level: its name `s`, its raw body
`dr` (a subterm of the original program syntax, well-formed with respect
to the names of the outer levels plus `s`), and its closed body `D`
obtained by substituting all outer levels into `dr`.
-/
private abbrev PumpEnv := List (native_String × SmtDatatype × SmtDatatype)

private def env_refs : PumpEnv -> RefList
  | [] => native_reflist_nil
  | (s, _, _) :: E => native_reflist_insert (env_refs E) s

private def env_close_dt : PumpEnv -> SmtDatatype -> SmtDatatype
  | [], X => X
  | (s, _, D) :: E, X => __smtx_dt_substitute s D (env_close_dt E X)

private def env_close_dtc : PumpEnv -> SmtDatatypeCons -> SmtDatatypeCons
  | [], X => X
  | (s, _, D) :: E, X => __smtx_dtc_substitute s D (env_close_dtc E X)

private def env_close_ty : PumpEnv -> SmtType -> SmtType
  | [], X => X
  | (s, _, D) :: E, X => __smtx_type_substitute s D (env_close_ty E X)

private def env_ok : PumpEnv -> Prop
  | [] => True
  | (s, dr, D) :: E =>
      native_reflist_contains (env_refs E) s = false ∧
      __smtx_dt_wf_rec dr dr = true ∧
      D = env_close_dt E dr ∧
      env_ok E

private def env_pump : PumpEnv -> Prop
  | [] => True
  | (s, dr, _D) :: E =>
      native_inhabited_type (SmtType.Datatype s dr) = true ∧
      __smtx_is_finite_datatype dr = false ∧
      env_pump E

private theorem env_refs_append :
    ∀ (E1 E2 : PumpEnv),
      env_refs (E1 ++ E2) = env_refs E1 ++ env_refs E2
  | [], _E2 => rfl
  | (s, dr, D) :: E1, E2 => by
      simp [env_refs, native_reflist_insert, env_refs_append E1 E2]

private theorem env_ok_append_right :
    ∀ (E1 E2 : PumpEnv), env_ok (E1 ++ E2) -> env_ok E2
  | [], _E2, h => h
  | (_s, _dr, _D) :: E1, E2, h => env_ok_append_right E1 E2 h.2.2.2

private theorem env_pump_append_right :
    ∀ (E1 E2 : PumpEnv), env_pump (E1 ++ E2) -> env_pump E2
  | [], _E2, h => h
  | (_s, _dr, _D) :: E1, E2, h => env_pump_append_right E1 E2 h.2.2

private theorem env_mem_split :
    ∀ (E : PumpEnv) (r : native_String),
      native_reflist_contains (env_refs E) r = true ->
        ∃ (E1 : PumpEnv) (dr D : SmtDatatype) (E2 : PumpEnv),
          E = E1 ++ (r, dr, D) :: E2
  | [], r, h => by
      simp [env_refs, native_reflist_nil, native_reflist_contains] at h
  | (s, dr, D) :: E, r, h => by
      by_cases hrs : r = s
      · subst hrs
        exact ⟨[], dr, D, E, rfl⟩
      · have hE : native_reflist_contains (env_refs E) r = true := by
          simp [env_refs, native_reflist_insert,
            native_reflist_contains] at h ⊢
          rcases h with h | h
          · exact False.elim (hrs h)
          · exact h
        rcases env_mem_split E r hE with ⟨E1, dr2, D2, E2, hEq⟩
        exact ⟨(s, dr, D) :: E1, dr2, D2, E2, by simp [hEq]⟩

private theorem env_close_dt_unref_of_not_contains (t : native_String) :
    ∀ (E : PumpEnv) (X : SmtDatatype),
      env_ok E ->
        native_reflist_contains (env_refs E) t = false ->
          smt_dt_unref t X = true ->
            smt_dt_unref t (env_close_dt E X) = true
  | [], _X, _hok, _ht, hX => hX
  | (s, dr, D) :: E, X, hok, ht, hX => by
      have htParts :
          t ≠ s ∧ native_reflist_contains (env_refs E) t = false := by
        simp [env_refs, native_reflist_insert,
          native_reflist_contains] at ht ⊢
        exact ht
      have hdrUnref : smt_dt_unref t dr = true := by
        apply dt_unref_of_wf_not_contains t dr
          (native_reflist_insert (env_refs E) s)
        · simp [native_reflist_insert, native_reflist_contains]
          exact ⟨htParts.1, by
            simpa [native_reflist_contains] using htParts.2⟩
        · exact hok.2.1
      have hDUnref : smt_dt_unref t D = true := by
        rw [hok.2.2.1]
        exact env_close_dt_unref_of_not_contains t E dr
          hok.2.2.2 htParts.2 hdrUnref
      have hXUnref : smt_dt_unref t (env_close_dt E X) = true :=
        env_close_dt_unref_of_not_contains t E X
          hok.2.2.2 htParts.2 hX
      exact dt_unref_substitute_other s D t hDUnref
        (env_close_dt E X) hXUnref

private theorem env_close_dt_unref_of_contains (t : native_String) :
    ∀ (E : PumpEnv) (X : SmtDatatype),
      env_ok E ->
        native_reflist_contains (env_refs E) t = true ->
          smt_dt_unref t (env_close_dt E X) = true
  | [], _X, _hok, ht => by
      simp [env_refs, native_reflist_nil, native_reflist_contains] at ht
  | (s, dr, D) :: E, X, hok, ht => by
      by_cases hts : t = s
      · subst hts
        exact dt_unref_substitute_self _ D (env_close_dt E X)
      · have htE : native_reflist_contains (env_refs E) t = true := by
          simp [env_refs, native_reflist_insert,
            native_reflist_contains] at ht ⊢
          rcases ht with h | h
          · exact False.elim (hts h)
          · exact h
        have hDUnref : smt_dt_unref t D = true := by
          rw [hok.2.2.1]
          exact env_close_dt_unref_of_contains t E dr hok.2.2.2 htE
        have hXUnref : smt_dt_unref t (env_close_dt E X) = true :=
          env_close_dt_unref_of_contains t E X hok.2.2.2 htE
        exact dt_unref_substitute_other s D t hDUnref
          (env_close_dt E X) hXUnref

/--
Self-containedness of closed bodies: the closed body of a coherent stack
level mentions no free type reference other than the level's own name.
-/
private theorem env_closed_body_unref
    (t s : native_String) (dr D : SmtDatatype) (E : PumpEnv)
    (hok : env_ok ((s, dr, D) :: E))
    (hts : t ≠ s) :
    smt_dt_unref t D = true := by
  rw [hok.2.2.1]
  by_cases htE : native_reflist_contains (env_refs E) t = true
  · exact env_close_dt_unref_of_contains t E dr hok.2.2.2 htE
  · have htE' : native_reflist_contains (env_refs E) t = false := by
      cases h : native_reflist_contains (env_refs E) t <;>
        simp [h] at htE ⊢
    have hdrUnref : smt_dt_unref t dr = true := by
      apply dt_unref_of_wf_not_contains t dr
        (native_reflist_insert (env_refs E) s)
      · simp [native_reflist_insert, native_reflist_contains]
        exact ⟨hts, by simpa [native_reflist_contains] using htE'⟩
      · exact hok.2.1
    exact env_close_dt_unref_of_not_contains t E dr
      hok.2.2.2 htE' hdrUnref

private theorem env_close_ty_typeref_not_contains :
    ∀ (E : PumpEnv) (r : native_String),
      native_reflist_contains (env_refs E) r = false ->
        env_close_ty E (SmtType.TypeRef r) = SmtType.TypeRef r
  | [], _r, _h => rfl
  | (s, dr, D) :: E, r, h => by
      have hParts :
          r ≠ s ∧ native_reflist_contains (env_refs E) r = false := by
        simp [env_refs, native_reflist_insert,
          native_reflist_contains] at h ⊢
        exact h
      have hsr : native_streq s r = false := by
        simp [native_streq]
        intro hEq
        exact hParts.1 hEq.symm
      rw [env_close_ty, env_close_ty_typeref_not_contains E r hParts.2]
      simp [__smtx_type_substitute, native_ite, hsr]

/--
Resolution of a legal type reference through a coherent stack: the
closure of `TypeRef r` is the closed datatype of the level named `r`.
-/
private theorem env_close_ty_typeref_resolve :
    ∀ (E1 : PumpEnv) (r : native_String) (dr D : SmtDatatype) (E2 : PumpEnv),
      env_ok (E1 ++ (r, dr, D) :: E2) ->
        env_close_ty (E1 ++ (r, dr, D) :: E2) (SmtType.TypeRef r) =
          SmtType.Datatype r D
  | [], r, dr, D, E2, hok => by
      have hNotE2 : native_reflist_contains (env_refs E2) r = false :=
        hok.1
      rw [List.nil_append, env_close_ty,
        env_close_ty_typeref_not_contains E2 r hNotE2]
      have hrr : native_streq r r = true := by simp [native_streq]
      simp [__smtx_type_substitute, native_ite, hrr]
  | (s1, dr1, D1) :: E1, r, dr, D, E2, hok => by
      have hok' : env_ok (E1 ++ (r, dr, D) :: E2) := hok.2.2.2
      have hMem :
          native_reflist_contains
            (env_refs (E1 ++ (r, dr, D) :: E2)) r = true := by
        rw [env_refs_append]
        simp [env_refs, native_reflist_insert, native_reflist_contains]
      have hs1r : s1 ≠ r := by
        intro hEq
        subst hEq
        have h1 :
            native_reflist_contains
              (env_refs (E1 ++ (s1, dr, D) :: E2)) s1 = false := hok.1
        rw [h1] at hMem
        simp at hMem
      have hs1rStr : native_streq s1 r = false := by
        simp [native_streq, hs1r]
      have hRec :=
        env_close_ty_typeref_resolve E1 r dr D E2 hok'
      rw [List.cons_append, env_close_ty, hRec]
      have hDUnref : smt_dt_unref s1 D = true := by
        rcases env_mem_split (E1 ++ (r, dr, D) :: E2) r hMem with
          ⟨F1, dr2, D2, F2, hEq⟩
        -- We resolve self-containedness directly on the given entry.
        have hokEntry : env_ok ((r, dr, D) :: E2) :=
          env_ok_append_right E1 _ hok'
        exact env_closed_body_unref s1 r dr D E2 hokEntry hs1r
      simp [__smtx_type_substitute, native_ite, hs1rStr,
        dt_substitute_eq_self_of_unref s1 (__smtx_dt_lift r D D1) D hDUnref]

private theorem env_close_dt_null :
    ∀ E : PumpEnv, env_close_dt E SmtDatatype.null = SmtDatatype.null
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_dt, env_close_dt_null E]
      rfl

private theorem env_close_dtc_unit :
    ∀ E : PumpEnv,
      env_close_dtc E SmtDatatypeCons.unit = SmtDatatypeCons.unit
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_dtc, env_close_dtc_unit E]
      rfl

private theorem env_close_dt_sum :
    ∀ (E : PumpEnv) (c : SmtDatatypeCons) (d : SmtDatatype),
      env_close_dt E (SmtDatatype.sum c d) =
        SmtDatatype.sum (env_close_dtc E c) (env_close_dt E d)
  | [], _c, _d => rfl
  | (s, _, D) :: E, c, d => by
      rw [env_close_dt, env_close_dt_sum E]
      rfl

private theorem env_close_dtc_cons :
    ∀ (E : PumpEnv) (T : SmtType) (c : SmtDatatypeCons),
      env_close_dtc E (SmtDatatypeCons.cons T c) =
        SmtDatatypeCons.cons (env_close_ty E T) (env_close_dtc E c)
  | [], _T, _c => rfl
  | (s, _, D) :: E, T, c => by
      rw [env_close_dtc, env_close_dtc_cons E]
      rfl

private theorem env_close_dt_append :
    ∀ (E : PumpEnv) (p q : SmtDatatype),
      env_close_dt E (dt_append p q) =
        dt_append (env_close_dt E p) (env_close_dt E q)
  | E, SmtDatatype.null, q => by
      rw [env_close_dt_null]
      rfl
  | E, SmtDatatype.sum c p, q => by
      rw [show dt_append (SmtDatatype.sum c p) q =
        SmtDatatype.sum c (dt_append p q) by rfl]
      rw [env_close_dt_sum, env_close_dt_sum, env_close_dt_append E p q]
      rfl

private theorem dt_constructor_offset_env_close :
    ∀ (E : PumpEnv) (p : SmtDatatype),
      dt_constructor_offset (env_close_dt E p) = dt_constructor_offset p
  | _E, SmtDatatype.null => by
      rw [env_close_dt_null]
  | E, SmtDatatype.sum c p => by
      rw [env_close_dt_sum]
      simp [dt_constructor_offset, dt_constructor_offset_env_close E p]

private theorem env_close_ty_eq_self_of_substitute_fix
    (T : SmtType)
    (hFix : ∀ (s : native_String) (d : SmtDatatype),
      __smtx_type_substitute s d T = T) :
    ∀ E : PumpEnv, env_close_ty E T = T
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_ty, env_close_ty_eq_self_of_substitute_fix T hFix E, hFix s D]

end Smtm
