import Cpc.Proofs.Canonical.TypeDefaultBasic
open SmtEval Smtm
namespace Smtm
set_option linter.unusedVariables false

/-!
# Finite well-formed types are defaultable

`fin_defaultable` / `cons_defaultable`: a finite, well-formed type (resp. constructor)
has a non-`NotValue` default.  This replaces the field-inhabitedness that the OLD
`__smtx_dt_cons_wf_rec` carried before the dtMutual refactor dropped its
`native_inhabited_type` gate.  The proof threads finiteness + well-formedness through
the three default builders via `__smtx_type_default_rec.induct`, using the
forcesNV-free shape relations `ShT`/`ShD`/`ShC` (finiteness excludes `TypeRef`, the
only `FieldRel.forcesNV` source, so the abstract `SubstStar` circularity is avoided).
-/

mutual
inductive ShT : SmtType → SmtType → Prop where
  | refl (T : SmtType) : ShT T T
  | dt {sF sU : native_String} {dF dU : SmtDatatype} :
      ShD dF dU → ShT (SmtType.Datatype sF dF) (SmtType.Datatype sU dU)
inductive ShD : SmtDatatype → SmtDatatype → Prop where
  | null : ShD SmtDatatype.null SmtDatatype.null
  | sum {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype} :
      ShC cF cU → ShD dF dU → ShD (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU)
inductive ShC : SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : ShC SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TF TU : SmtType} {cF cU : SmtDatatypeCons} :
      ShT TF TU → ShC cF cU → ShC (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons TU cU)
end

theorem ShC_refl : ∀ c, ShC c c
  | SmtDatatypeCons.unit => ShC.unit
  | SmtDatatypeCons.cons T c => ShC.cons (ShT.refl T) (ShC_refl c)
theorem ShD_refl : ∀ d, ShD d d
  | SmtDatatype.null => ShD.null
  | SmtDatatype.sum c d => ShD.sum (ShC_refl c) (ShD_refl d)

-- diagonal: substituting a finite type/datatype/cons preserves its shape
mutual
theorem ShT_subst_fin (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType, __smtx_is_finite_type T = true → ShT (__smtx_type_substitute s d T) T
  | SmtType.Datatype s2 d2, hfin => by
      have hfind2 : __smtx_is_finite_datatype d2 = true := by
        simpa [__smtx_is_finite_type] using hfin
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s s2 = true
      · rw [native_ite, if_pos hEq]; exact ShT.dt (ShD_refl d2)
      · rw [native_ite, if_neg hEq]; exact ShT.dt (ShD_subst_fin s _ d2 hfind2)
  | SmtType.TypeRef s2, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.None, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.Int, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.Real, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.RegLan, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.Seq A, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.USort i, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.FunType A B, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.DtcAppType A B, hfin => by simp [__smtx_is_finite_type] at hfin
  | SmtType.Bool, hfin => by simpa [__smtx_type_substitute] using ShT.refl SmtType.Bool
  | SmtType.BitVec w, hfin => by simpa [__smtx_type_substitute] using ShT.refl (SmtType.BitVec w)
  | SmtType.Char, hfin => by simpa [__smtx_type_substitute] using ShT.refl SmtType.Char
  | SmtType.Map A B, hfin => by simpa [__smtx_type_substitute] using ShT.refl (SmtType.Map A B)
  | SmtType.Set A, hfin => by simpa [__smtx_type_substitute] using ShT.refl (SmtType.Set A)
theorem ShC_subst_fin (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons, __smtx_is_finite_datatype_cons c = true → ShC (__smtx_dtc_substitute s d c) c
  | SmtDatatypeCons.unit, hfin => by simpa [__smtx_dtc_substitute] using ShC.unit
  | SmtDatatypeCons.cons T c, hfin => by
      have hp : __smtx_is_finite_type T = true ∧ __smtx_is_finite_datatype_cons c = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hfin
      simpa [__smtx_dtc_substitute] using ShC.cons (ShT_subst_fin s d T hp.1) (ShC_subst_fin s d c hp.2)
theorem ShD_subst_fin (s : native_String) (d : SmtDatatype) :
    ∀ D : SmtDatatype, __smtx_is_finite_datatype D = true → ShD (__smtx_dt_substitute s d D) D
  | SmtDatatype.null, hfin => by simpa [__smtx_dt_substitute] using ShD.null
  | SmtDatatype.sum c D, hfin => by
      have hp : __smtx_is_finite_datatype_cons c = true ∧ __smtx_is_finite_datatype D = true := by
        simpa [__smtx_is_finite_datatype, native_and] using hfin
      simpa [__smtx_dt_substitute] using ShD.sum (ShC_subst_fin s d c hp.1) (ShD_subst_fin s d D hp.2)
end

-- preserve an existing shape relation when substituting the folded side
mutual
theorem ShT_substF (s : native_String) (d : SmtDatatype) :
    ∀ {TF TU : SmtType}, ShT TF TU → __smtx_is_finite_type TU = true →
      ShT (__smtx_type_substitute s d TF) TU
  | _, TU, ShT.refl _, hfin => ShT_subst_fin s d TU hfin
  | _, _, @ShT.dt sF sU dF dU hd, hfin => by
      have hfindU : __smtx_is_finite_datatype dU = true := by
        simpa [__smtx_is_finite_type] using hfin
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s sF = true
      · rw [native_ite, if_pos hEq]; exact ShT.dt hd
      · rw [native_ite, if_neg hEq]; exact ShT.dt (ShD_substF s _ hd hfindU)
theorem ShC_substF (s : native_String) (d : SmtDatatype) :
    ∀ {cF cU : SmtDatatypeCons}, ShC cF cU → __smtx_is_finite_datatype_cons cU = true →
      ShC (__smtx_dtc_substitute s d cF) cU
  | _, _, ShC.unit, hfin => by simpa [__smtx_dtc_substitute] using ShC.unit
  | _, _, @ShC.cons TF TU cF cU hT hC, hfin => by
      have hp : __smtx_is_finite_type TU = true ∧ __smtx_is_finite_datatype_cons cU = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hfin
      simpa [__smtx_dtc_substitute] using ShC.cons (ShT_substF s d hT hp.1) (ShC_substF s d hC hp.2)
theorem ShD_substF (s : native_String) (d : SmtDatatype) :
    ∀ {dF dU : SmtDatatype}, ShD dF dU → __smtx_is_finite_datatype dU = true →
      ShD (__smtx_dt_substitute s d dF) dU
  | _, _, ShD.null, hfin => by simpa [__smtx_dt_substitute] using ShD.null
  | _, _, @ShD.sum cF cU dF dU hC hD, hfin => by
      have hp : __smtx_is_finite_datatype_cons cU = true ∧ __smtx_is_finite_datatype dU = true := by
        simpa [__smtx_is_finite_datatype, native_and] using hfin
      simpa [__smtx_dt_substitute] using ShD.sum (ShC_substF s d hC hp.1) (ShD_substF s d hD hp.2)
end

-- local helpers (mirror CardinalityAssumptions)
private theorem nveq_false {a b : SmtValue} (h : a ≠ b) : native_veq a b = false := by
  simp [native_veq, h]
private theorem ne_none_inh {T : SmtType} (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  intro hN; subst T; simp [native_inhabited_type, native_Teq, native_not, native_and] at h
private theorem tdef_ne_nv {T : SmtType} (hInh : native_inhabited_type T = true)
    (hT : T ≠ SmtType.None) : __smtx_type_default T ≠ SmtValue.NotValue := by
  have hP : native_Teq T SmtType.None = false ∧
      native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true := by
    simpa [native_inhabited_type, native_and, native_not] using hInh
  have hTy : __smtx_typeof_value (__smtx_type_default T) = T := by simpa [native_Teq] using hP.2
  intro hEq; rw [hEq] at hTy; simp [__smtx_typeof_value] at hTy; exact hT hTy.symm
private theorem dd_select
    (s : native_String) (d : SmtDatatype) (n : native_Nat)
    (cF cU : SmtDatatypeCons) (DF DU : SmtDatatype)
    (hNe : __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU ≠ SmtValue.NotValue) :
    __smtx_datatype_default s d n (SmtDatatype.sum cF DF) (SmtDatatype.sum cU DU) =
      __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU := by
  have hf : native_veq (__smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU)
      SmtValue.NotValue = false := nveq_false hNe
  rw [__smtx_datatype_default]; simp [native_ite, native_not, hf]

theorem fin_defaultable :
    ∀ V T : SmtType, ShT V T → __smtx_is_finite_type T = true →
      ∀ refs, __smtx_type_wf_rec T refs = true →
        __smtx_type_default_rec V T ≠ SmtValue.NotValue := by
  refine __smtx_type_default_rec.induct
    (motive1 := fun V T => ShT V T → __smtx_is_finite_type T = true →
      ∀ refs, __smtx_type_wf_rec T refs = true → __smtx_type_default_rec V T ≠ SmtValue.NotValue)
    (motive2 := fun s d n DF DU => ShD DF DU → __smtx_is_finite_datatype DU = true →
      ∀ refs, __smtx_dt_wf_rec DU refs = true → __smtx_datatype_default s d n DF DU ≠ SmtValue.NotValue)
    (motive3 := fun v cF cU => ShC cF cU → __smtx_is_finite_datatype_cons cU = true →
      ∀ refs, __smtx_dt_cons_wf_rec cU refs = true → v ≠ SmtValue.NotValue →
        __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro sF dF sU dU ih2 hsh hfin refs hwf
    rw [__smtx_type_default_rec]
    have hfinDU : __smtx_is_finite_datatype dU = true := by simpa [__smtx_is_finite_type] using hfin
    have hwfDU : __smtx_dt_wf_rec dU (native_reflist_insert refs sU) = true := by
      by_cases hc : native_reflist_contains refs sU = true
      · simp [__smtx_type_wf_rec, native_ite, hc] at hwf
      · simpa [__smtx_type_wf_rec, native_ite, hc] using hwf
    have hShD : ShD dF dU := by cases hsh with | refl => exact ShD_refl _ | dt h => exact h
    exact ih2 (ShD_substF sF dF hShD hfinDU) hfinDU (native_reflist_insert refs sU) hwfDU
  · intro V hsh hfin refs hwf; rw [__smtx_type_default_rec]; exact fun h => by cases h
  · intro V hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V w hsh hfin refs hwf; rw [__smtx_type_default_rec]; exact fun h => by cases h
  · intro V hsh hfin refs hwf; rw [__smtx_type_default_rec]; exact fun h => by cases h
  · intro V T U ih hsh hfin refs hwf
    have hInhU : native_inhabited_type U = true := by
      simp [__smtx_type_wf_rec, native_and] at hwf; exact hwf.2.2.1
    have hv0 : native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = false := by
      apply nveq_false
      have := tdef_ne_nv hInhU (ne_none_inh hInhU)
      simpa [__smtx_type_default] using this
    rw [__smtx_type_default_rec]; simp [native_ite, hv0]
  · intro V T hsh hfin refs hwf; rw [__smtx_type_default_rec]; exact fun h => by cases h
  · intro V T hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V i hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V T U hsh hfin refs hwf; simp [__smtx_is_finite_type] at hfin
  · intro V T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hsh hfin refs hwf
    cases T with
    | Datatype a b =>
        cases hsh with
        | refl => exact (h1 a b a b rfl rfl).elim
        | dt _ => exact (h1 _ _ a b rfl rfl).elim
    | _ => simp_all [__smtx_is_finite_type]
  · intro s d n cF dF cU dU ih3 ih2 hsh hfin refs hwf
    have hShC : ShC cF cU := by cases hsh with | sum hc _ => exact hc
    have hfinCons : __smtx_is_finite_datatype_cons cU = true := by
      simp [__smtx_is_finite_datatype, native_and] at hfin; exact hfin.1
    have hwfCons : __smtx_dt_cons_wf_rec cU refs = true := by
      by_cases hcw : __smtx_dt_cons_wf_rec cU refs = true
      · exact hcw
      · exfalso; cases dU <;> simp [__smtx_dt_wf_rec, native_ite, hcw] at hwf
    have hcons : __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU ≠ SmtValue.NotValue :=
      ih3 hShC hfinCons refs hwfCons (by intro h; cases h)
    rw [dd_select s d n cF cU dF dU hcons]; exact hcons
  · intro s d n dF dU hne hsh hfin refs hwf
    cases hsh with
    | null => simp [__smtx_dt_wf_rec] at hwf
    | sum hc hd => exact (hne _ _ _ _ rfl rfl).elim
  · intro v hsh hfin refs hwf hvne
    simpa [__smtx_datatype_cons_default] using hvne
  · intro v TF cF TU cU _v0 ih1 ih3 hsh hfin refs hwf hvne
    have hShT : ShT TF TU := by cases hsh with | cons hT _ => exact hT
    have hShCtail : ShC cF cU := by cases hsh with | cons _ hC => exact hC
    have hfinParts : __smtx_is_finite_type TU = true ∧ __smtx_is_finite_datatype_cons cU = true := by
      simpa [__smtx_is_finite_datatype_cons, native_and] using hfin
    have hwfTU : __smtx_type_wf_rec TU refs = true := by
      by_cases h : __smtx_type_wf_rec TU refs = true
      · exact h
      · exfalso; cases TU <;>
          simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type, __smtx_type_wf_rec]
    have hwfTail : __smtx_dt_cons_wf_rec cU refs = true := by
      by_cases h : __smtx_dt_cons_wf_rec cU refs = true
      · exact h
      · exfalso; cases TU <;>
          simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type]
    have hfieldNe : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue :=
      ih1 hShT hfinParts.1 refs hwfTU
    have hfieldFalse : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = false :=
      nveq_false hfieldNe
    rw [__smtx_datatype_cons_default, native_ite, if_neg (by simp [hfieldFalse])]
    exact ih3 hShCtail hfinParts.2 refs hwfTail (by intro h; cases h)
  · intro v cF cU hne1 hne2 hsh hfin refs hwf hvne
    cases hsh with
    | unit => exact (hne1 rfl rfl).elim
    | cons hT hC => exact (hne2 _ _ _ _ rfl rfl).elim

-- constructor-level defaultability (the witnesses need this)
theorem cons_defaultable :
    ∀ (cU cF : SmtDatatypeCons), ShC cF cU →
      __smtx_is_finite_datatype_cons cU = true →
      ∀ refs, __smtx_dt_cons_wf_rec cU refs = true →
      ∀ v, v ≠ SmtValue.NotValue →
        __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, cF, hsh, hfin, refs, hwf, v, hv => by
      cases hsh; simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons TU cU, cF, hsh, hfin, refs, hwf, v, hv => by
      cases hsh with
      | @cons TF _ cF' _ hT hC =>
        have hp : __smtx_is_finite_type TU = true ∧ __smtx_is_finite_datatype_cons cU = true := by
          simpa [__smtx_is_finite_datatype_cons, native_and] using hfin
        have hwfTU : __smtx_type_wf_rec TU refs = true := by
          by_cases h : __smtx_type_wf_rec TU refs = true
          · exact h
          · exfalso; cases TU <;>
              simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type, __smtx_type_wf_rec]
        have hwfTail : __smtx_dt_cons_wf_rec cU refs = true := by
          by_cases h : __smtx_dt_cons_wf_rec cU refs = true
          · exact h
          · exfalso; cases TU <;>
              simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type]
        have hfieldNe := fin_defaultable TF TU hT hp.1 refs hwfTU
        have hff := nveq_false hfieldNe
        rw [__smtx_datatype_cons_default, native_ite, if_neg (by simp [hff])]
        exact cons_defaultable cU cF' hC hp.2 refs hwfTail _ (by intro h; cases h)
  termination_by cU => sizeOf cU
  decreasing_by all_goals (try simp_wf); all_goals omega

end Smtm
