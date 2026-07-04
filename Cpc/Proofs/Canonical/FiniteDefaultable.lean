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

private theorem finite_dt_cons_of_finite_sum {c : SmtDatatypeCons} {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = true) :
    __smtx_is_finite_datatype_cons c = true := by
  have hP : __smtx_is_finite_datatype_cons c = true ∧ __smtx_is_finite_datatype d = true := by
    simpa [__smtx_is_finite_datatype, native_and] using hFin
  exact hP.1

private theorem dt_wf_cons_of_wf {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  cases hc : __smtx_dt_cons_wf_rec cF cU <;>
    simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

private theorem wf_parts_of_cons_diag {T : SmtType} {c : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c)
        (SmtDatatypeCons.cons T c) = true) :
    native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true ∧
      __smtx_dt_cons_wf_rec c c = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_and, native_ite] at h ⊢
  all_goals exact ⟨h.1.1, h.1.2, h.2⟩

-- substitution is the identity on finite types (no TypeRef ⇒ nothing to substitute),
-- collapsing the folded/unfolding distinction to the diagonal for finite datatypes
mutual
theorem subst_T_fin_id (s : native_String) :
    ∀ (d0 : SmtDatatype) (T : SmtType), __smtx_is_finite_type T = true →
      __smtx_type_substitute s d0 T = T
  | d0, SmtType.Datatype s2 d2, hfin => by
      have hf2 : __smtx_is_finite_datatype d2 = true := by simpa [__smtx_is_finite_type] using hfin
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s s2 = true
      · rw [native_ite, if_pos hEq]
      · rw [native_ite, if_neg hEq, subst_D_fin_id s _ d2 hf2]
  | d0, SmtType.TypeRef s2, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.None, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.Int, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.Real, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.RegLan, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.Seq A, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.USort i, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.FunType A B, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.DtcAppType A B, hfin => by simp [__smtx_is_finite_type] at hfin
  | d0, SmtType.Bool, hfin => by simp [__smtx_type_substitute]
  | d0, SmtType.BitVec w, hfin => by simp [__smtx_type_substitute]
  | d0, SmtType.Char, hfin => by simp [__smtx_type_substitute]
  | d0, SmtType.Map A B, hfin => by simp [__smtx_type_substitute]
  | d0, SmtType.Set A, hfin => by simp [__smtx_type_substitute]
theorem subst_C_fin_id (s : native_String) :
    ∀ (d0 : SmtDatatype) (c : SmtDatatypeCons), __smtx_is_finite_datatype_cons c = true →
      __smtx_dtc_substitute s d0 c = c
  | d0, SmtDatatypeCons.unit, hfin => by simp [__smtx_dtc_substitute]
  | d0, SmtDatatypeCons.cons T c, hfin => by
      have hp : __smtx_is_finite_type T = true ∧ __smtx_is_finite_datatype_cons c = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hfin
      simp [__smtx_dtc_substitute, subst_T_fin_id s d0 T hp.1, subst_C_fin_id s d0 c hp.2]
theorem subst_D_fin_id (s : native_String) :
    ∀ (d0 : SmtDatatype) (D : SmtDatatype), __smtx_is_finite_datatype D = true →
      __smtx_dt_substitute s d0 D = D
  | d0, SmtDatatype.null, hfin => by simp [__smtx_dt_substitute]
  | d0, SmtDatatype.sum c D, hfin => by
      have hp : __smtx_is_finite_datatype_cons c = true ∧ __smtx_is_finite_datatype D = true := by
        simpa [__smtx_is_finite_datatype, native_and] using hfin
      simp [__smtx_dt_substitute, subst_C_fin_id s d0 c hp.1, subst_D_fin_id s d0 D hp.2]
end

-- Finite defaultability under the refactored full/unfold well-formedness.
-- The type-level theorem requires inhabitedness: finite + diagonal `wf_rec`
-- alone is not enough, since the empty datatype is finite and diagonal-well-formed
-- but has no default value.
mutual

theorem fin_defaultable :
    ∀ V T : SmtType, ShT V T → __smtx_is_finite_type T = true →
      __smtx_type_wf_rec T T = true → native_inhabited_type T = true →
        __smtx_type_default_rec V T ≠ SmtValue.NotValue := by
  intro V T hSh hFin hWf hInh
  cases hSh with
  | refl T =>
      have hTne := ne_none_inh hInh
      simpa [__smtx_type_default] using tdef_ne_nv hInh hTne
  | @dt sF sU dF dU hD =>
      have hFinD : __smtx_is_finite_datatype dU = true := by
        simpa [__smtx_is_finite_type] using hFin
      have hSubU : __smtx_dt_substitute sU dU dU = dU :=
        subst_D_fin_id sU dU dU hFinD
      have hWfD : __smtx_dt_wf_rec dU dU = true := by
        simpa [__smtx_type_wf_rec, hSubU] using hWf
      have hShape : ShD (__smtx_dt_substitute sF dF dF) dU :=
        ShD_substF sF dF hD hFinD
      cases dU with
      | null =>
          simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec,
            __smtx_datatype_default, __smtx_typeof_value, native_Teq, native_not,
            native_and] at hInh
        | sum cU dUTail =>
            cases hSubF : __smtx_dt_substitute sF dF dF with
            | null =>
                have hShape' : ShD SmtDatatype.null (SmtDatatype.sum cU dUTail) := by
                  simpa [hSubF] using hShape
                cases hShape'
            | sum cF dFTail =>
                have hShape' : ShD (SmtDatatype.sum cF dFTail) (SmtDatatype.sum cU dUTail) := by
                  simpa [hSubF] using hShape
                cases hShape' with
                | sum hC hDTail =>
                    have hConsFin : __smtx_is_finite_datatype_cons cU = true :=
                      finite_dt_cons_of_finite_sum hFinD
                    have hConsWf : __smtx_dt_cons_wf_rec cU cU = true :=
                      dt_wf_cons_of_wf hWfD
                    have hSeedNe : SmtValue.DtCons sF dF 0 ≠ SmtValue.NotValue := by
                      intro h; cases h
                    have hConsNe :
                        __smtx_datatype_cons_default (SmtValue.DtCons sF dF 0)
                          cF cU ≠ SmtValue.NotValue :=
                      cons_defaultable cU cF hC hConsFin hConsWf
                        (SmtValue.DtCons sF dF 0) hSeedNe
                    rw [__smtx_type_default_rec, hSubF]
                    rw [dd_select sF dF 0 cF cU dFTail dUTail hConsNe]
                    exact hConsNe

-- constructor-level defaultability (the witnesses need this)
theorem cons_defaultable :
    ∀ (cU cF : SmtDatatypeCons), ShC cF cU →
      __smtx_is_finite_datatype_cons cU = true →
      __smtx_dt_cons_wf_rec cU cU = true →
      ∀ v, v ≠ SmtValue.NotValue →
        __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit, ShC.unit, _hFin, _hWf, v, hv => by
      simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons TU cU, SmtDatatypeCons.cons TF cF,
      ShC.cons hT hC, hFin, hWf, v, hv => by
      have hFinParts :
          __smtx_is_finite_type TU = true ∧ __smtx_is_finite_datatype_cons cU = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hFin
      have hWfParts := wf_parts_of_cons_diag hWf
      have hFieldNe :
          __smtx_type_default_rec TF TU ≠ SmtValue.NotValue :=
        fin_defaultable TF TU hT hFinParts.1 hWfParts.2.1 hWfParts.1
      have hFieldVeq :
          native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = false :=
        nveq_false hFieldNe
      have hApplyNe :
          SmtValue.Apply v (__smtx_type_default_rec TF TU) ≠ SmtValue.NotValue := by
        intro h; cases h
      rw [__smtx_datatype_cons_default]
      simp [native_ite, hFieldVeq]
      exact cons_defaultable cU cF hC hFinParts.2 hWfParts.2.2
        (SmtValue.Apply v (__smtx_type_default_rec TF TU)) hApplyNe

end

end Smtm
