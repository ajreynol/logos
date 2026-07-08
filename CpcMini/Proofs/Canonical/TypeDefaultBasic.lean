import CpcMini.SmtModel
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm

/-!
Basic facts about `__smtx_type_default` (two parallel types `V`/`T`,
via `__smtx_type_default_rec`).

* `type_default_notvalue_or_typed` (Goal 1): the default value is either `NotValue`
  or a value whose type is the input type.
* `type_default_canonical_of_typed` (Goal 2): the default value is canonical.

Both reduce to the diagonal instance of the combined kernel `datatype_kernel_rec`,
which is proved by the functional induction `__smtx_type_default_rec.induct` over the
four mutually-recursive default builders. In the declaration-based datatype
representation the fold side is the `__smtx_dt_resolve`d copy of the unresolved side,
so the invariants are plain equalities: the datatype walk keeps
`DF = __smtx_dt_resolve DU dd` together with the `drop_cons` position bookkeeping,
and the constructor walk keeps `cF = __smtx_dtc_resolve cU dd`. Recursive (`TypeRef`)
fields force `NotValue` directly, and the `chainType` ↔ `typeof_dt_cons_value_rec`
correspondence provides the typing of partially-applied constructor values.
-/

-- TypeRef as 2nd arg forces NotValue
theorem rec_typeref_nv (s2 : native_String) (V : SmtType) :
    __smtx_type_default_rec V (SmtType.TypeRef s2) = SmtValue.NotValue := by
  simp [__smtx_type_default_rec]

-- Inversion for a resolved constructor-field list.
theorem dtc_resolve_cons_inv (dd : SmtDatatypeDecl) {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : SmtDatatypeCons.cons TF cF = __smtx_dtc_resolve (SmtDatatypeCons.cons TU cU) dd) :
    cF = __smtx_dtc_resolve cU dd ∧ (TF = TU ∨ ∃ s2, TU = SmtType.TypeRef s2) := by
  cases TU
  case TypeRef s2 =>
    simp only [__smtx_dtc_resolve] at h
    injection h with h1 h2
    exact ⟨h2, Or.inr ⟨s2, rfl⟩⟩
  all_goals
    simp only [__smtx_dtc_resolve] at h
    injection h with h1 h2
    exact ⟨h2, Or.inl h1⟩

def chainType : SmtDatatypeCons → SmtType → SmtType
  | SmtDatatypeCons.unit, base => base
  | SmtDatatypeCons.cons T c, base => SmtType.DtcAppType T (chainType c base)

theorem chainType_eq (base : SmtType) :
    ∀ (c : SmtDatatypeCons) (d' : SmtDatatype),
      __smtx_typeof_dt_cons_value_rec base (SmtDatatype.sum c d') native_nat_zero = chainType c base
  | SmtDatatypeCons.unit, d' => by simp [__smtx_typeof_dt_cons_value_rec, chainType]
  | SmtDatatypeCons.cons T c, d' => by
      simp [__smtx_typeof_dt_cons_value_rec, chainType, chainType_eq base c d']

def drop_cons : SmtDatatype → native_Nat → SmtDatatype
  | SmtDatatype.sum c d, Nat.succ n => drop_cons d n
  | D, _ => D

theorem drop_cons_succ (X : SmtDatatype) (n : native_Nat) :
    drop_cons X (Nat.succ n) =
      (match drop_cons X n with
       | SmtDatatype.sum _ t => t
       | D => D) := by
  induction n generalizing X with
  | zero => cases X <;> simp [drop_cons]
  | succ n ih => cases X <;> simp [drop_cons, ih]

theorem drop_lemma (base : SmtType) :
    ∀ (DSUB : SmtDatatype) (n : native_Nat) (cF : SmtDatatypeCons) (DF' : SmtDatatype),
      drop_cons DSUB n = SmtDatatype.sum cF DF' →
      __smtx_typeof_dt_cons_value_rec base DSUB n = chainType cF base
  | DSUB, Nat.zero, cF, DF', h => by
      simp only [drop_cons] at h
      rw [h]; exact chainType_eq base cF DF'
  | SmtDatatype.sum c d, Nat.succ n, cF, DF', h => by
      simp only [drop_cons] at h
      simp only [__smtx_typeof_dt_cons_value_rec]
      exact drop_lemma base d n cF DF' h
  | SmtDatatype.null, Nat.succ n, cF, DF', h => by
      simp [drop_cons] at h


theorem drop_cons_zero (X : SmtDatatype) : drop_cons X 0 = X := by cases X <;> rfl

-- `drop_cons` commutes with `__smtx_dt_resolve`.
theorem drop_cons_resolve (dd : SmtDatatypeDecl) :
    ∀ (n : native_Nat) (D : SmtDatatype),
      drop_cons (__smtx_dt_resolve D dd) n = __smtx_dt_resolve (drop_cons D n) dd := by
  intro n
  induction n with
  | zero => intro D; rw [drop_cons_zero, drop_cons_zero]
  | succ n ih =>
      intro D
      cases D with
      | null => simp [__smtx_dt_resolve, drop_cons]
      | sum c d => simp only [__smtx_dt_resolve, drop_cons]; exact ih d

theorem datatype_kernel_rec : ∀ V T : SmtType,
    V = T →
    __smtx_type_default_rec V T = SmtValue.NotValue ∨
    (__smtx_typeof_value (__smtx_type_default_rec V T) = V ∧
     __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true) := by
  refine __smtx_type_default_rec.induct
    (motive1 := fun V T => V = T →
      __smtx_type_default_rec V T = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_type_default_rec V T) = V ∧
       __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true))
    (motive2 := fun s dd ddF ddU =>
      ddF = ddU → __smtx_dd_lookup s ddF = __smtx_dd_lookup s dd →
      __smtx_datatype_decl_default s dd ddF ddU = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_datatype_decl_default s dd ddF ddU) = SmtType.Datatype s dd ∧
       __smtx_value_canonical_bool (__smtx_datatype_decl_default s dd ddF ddU) = true))
    (motive3 := fun s dd n DF DU =>
      DF = __smtx_dt_resolve DU dd →
      DU = drop_cons (__smtx_dd_lookup s dd) n →
      __smtx_datatype_default s dd n DF DU = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_datatype_default s dd n DF DU) = SmtType.Datatype s dd ∧
       __smtx_value_canonical_bool (__smtx_datatype_default s dd n DF DU) = true))
    (motive4 := fun v cF cU =>
      ∀ (base : SmtType) (dd : SmtDatatypeDecl),
      cF = __smtx_dtc_resolve cU dd → __smtx_typeof_value v = chainType cF base →
      __smtx_value_canonical_bool v = true →
      __smtx_datatype_cons_default v cF cU = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_datatype_cons_default v cF cU) = base ∧
       __smtx_value_canonical_bool (__smtx_datatype_cons_default v cF cU) = true))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro sF ddF sU ddU ih2 hVT
    injection hVT with hs hdd
    rw [__smtx_type_default_rec]
    exact ih2 hdd rfl
  · intro V hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_re_canonical, native_re_none]
  · intro V w hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_nat_to_int, native_and, native_zleq, native_zeq, native_mod_total, native_int_to_nat, native_ite]
  · intro V hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_char_valid, native_ite]
  · intro V T U ih hVT
    subst hVT
    rw [__smtx_type_default_rec]
    by_cases hv : native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = true
    · left; rw [native_ite, if_pos hv]
    · rw [native_ite, if_neg hv]
      rcases ih rfl with h0 | ⟨h1, h2⟩
      · exact absurd (by simp [native_veq, h0]) hv
      · right; refine ⟨?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value, h1]
        · simp [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical, h1, h2, native_veq, native_and, native_ite, __smtx_type_default, decide_true, Bool.and_true, ite_self]
  · intro V T hVT
    subst hVT
    right; refine ⟨?_, ?_⟩
    · simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]
    · simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical, __smtx_msm_get_default, native_and, native_veq, native_ite, __smtx_typeof_value, __smtx_type_default]
  · intro V T hVT
    subst hVT
    right; refine ⟨?_, ?_⟩
    · simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_seq_value]
    · simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_seq_canonical]
  · intro V i hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V T U hVT; subst hVT; right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hVT
    left
    cases T with
    | None => simp [__smtx_type_default_rec]
    | TypeRef s => simp [__smtx_type_default_rec]
    | DtcAppType A B => simp [__smtx_type_default_rec]
    | Datatype a b => exact (h1 a b a b hVT rfl).elim
    | _ => simp_all
  · intro s dd sF dF ddF sU dU ddU ih3 ih2 hEq hLk
    injection hEq with hs hd hdd
    rw [__smtx_datatype_decl_default]
    by_cases hstr : native_streq s sF = true
    · rw [native_ite, if_pos hstr]
      have hlk : __smtx_dd_lookup s dd = dF := by
        rw [← hLk]; simp only [__smtx_dd_lookup]; rw [native_ite, if_pos hstr]
      exact ih3 (by rw [hd]) (by rw [drop_cons_zero, hlk]; exact hd.symm)
    · rw [native_ite, if_neg hstr]
      have hLk' : __smtx_dd_lookup s ddF = __smtx_dd_lookup s dd := by
        rw [← hLk]; simp only [__smtx_dd_lookup]; rw [native_ite, if_neg hstr]
      exact ih2 hdd hLk'
  · intro s dd ddF ddU hne hEq hLk
    subst hEq
    cases ddF with
    | nil => left; simp [__smtx_datatype_decl_default]
    | cons a b c => exact (hne a b c a b c rfl rfl).elim
  · intro s dd n cF dF cU dU ih4 ih3 hRes hDrop
    simp only [__smtx_dt_resolve] at hRes
    injection hRes with hcF hdF
    have htypeofDtCons : __smtx_typeof_value (SmtValue.DtCons s dd n) = chainType cF (SmtType.Datatype s dd) := by
      simp only [__smtx_typeof_value]
      apply drop_lemma (SmtType.Datatype s dd) (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) n cF (__smtx_dt_resolve dU dd)
      rw [drop_cons_resolve, ← hDrop]
      simp only [__smtx_dt_resolve]
      rw [← hcF]
    have hcanonDtCons : __smtx_value_canonical_bool (SmtValue.DtCons s dd n) = true := by
      simp [__smtx_value_canonical_bool]
    have hdrop' : dU = drop_cons (__smtx_dd_lookup s dd) (Nat.succ n) := by
      rw [drop_cons_succ, ← hDrop]
    rw [__smtx_datatype_default]
    simp only [native_not, native_veq, native_ite]
    split
    · next hcond =>
      rcases ih4 (SmtType.Datatype s dd) dd hcF htypeofDtCons hcanonDtCons with hNV | hTy
      · rw [hNV] at hcond; simp at hcond
      · right; exact hTy
    · next hcond =>
      rcases ih4 (SmtType.Datatype s dd) dd hcF htypeofDtCons hcanonDtCons with hNV | hTy
      · exact ih3 hdF hdrop'
      · exfalso
        have hv0ne : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) cF cU ≠ SmtValue.NotValue := by
          intro hc; rw [hc] at hTy; simp [__smtx_typeof_value] at hTy
        simp [hv0ne] at hcond
  · intro s dd n dF dU hne hRes hDrop
    cases dU with
    | null =>
        simp only [__smtx_dt_resolve] at hRes
        subst hRes
        left; simp [__smtx_datatype_default]
    | sum cU' dU' =>
        simp only [__smtx_dt_resolve] at hRes
        exact (hne _ _ cU' dU' hRes rfl).elim
  · intro v base dd hres htypeof hcanon
    right
    refine ⟨?_, ?_⟩
    · simpa [__smtx_datatype_cons_default, chainType] using htypeof
    · simpa [__smtx_datatype_cons_default] using hcanon
  · intro v TF cF TU cU _v0 ih1 ih4 base dd hres htypeof hcanon
    obtain ⟨hcF, hTF⟩ := dtc_resolve_cons_inv dd hres
    rw [__smtx_datatype_cons_default]
    by_cases hv : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true
    · left; rw [native_ite, if_pos hv]
    · rw [native_ite, if_neg hv]
      rcases hTF with hTF | ⟨s2, hTU⟩
      · subst hTF
        rcases ih1 rfl with hNV | ⟨hTy, hCanonField⟩
        · exact absurd (by simp [native_veq, hNV]) hv
        · have hTFne : TF ≠ SmtType.None := by
            intro hNone; rw [hNone] at hv; simp [__smtx_type_default_rec, native_veq] at hv
          have htypeofApply : __smtx_typeof_value (SmtValue.Apply v (__smtx_type_default_rec TF TF)) = chainType cF base := by
            have hchain : chainType (SmtDatatypeCons.cons TF cF) base = SmtType.DtcAppType TF (chainType cF base) := rfl
            rw [hchain] at htypeof
            simp only [__smtx_typeof_value, htypeof, hTy, __smtx_typeof_apply_value,
                       __smtx_typeof_guard, native_Teq, native_ite, decide_true, if_true]
            simp [hTFne]
          have hcanonApply : __smtx_value_canonical_bool (SmtValue.Apply v (__smtx_type_default_rec TF TF)) = true := by
            simp [__smtx_value_canonical_bool, hcanon, hCanonField, native_and]
          exact ih4 base dd hcF htypeofApply hcanonApply
      · subst hTU
        exact absurd (by simp [native_veq, rec_typeref_nv]) hv
  · intro v cF cU hne1 hne2 base dd hres htypeof hcanon
    exfalso
    cases cU with
    | unit =>
        simp only [__smtx_dtc_resolve] at hres
        exact hne1 hres rfl
    | cons TU cU' =>
        cases TU <;> simp only [__smtx_dtc_resolve] at hres <;>
          exact hne2 _ _ _ _ hres rfl

/-- Diagonal instance of the kernel: the default value of any type is either
`NotValue`, or a canonical value whose type is the input type. -/
theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue
      ∨ __smtx_typeof_value (__smtx_type_default T) = T := by
  unfold __smtx_type_default
  rcases datatype_kernel_rec T T rfl with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Canonicity of the default value. The kernel makes this unconditional, so the
typing hypothesis `h` is not needed (kept for the original interface). -/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  unfold __smtx_type_default
  rcases datatype_kernel_rec T T rfl with h0 | ⟨_, hc⟩
  · rw [h0]; simp [__smtx_value_canonical_bool]
  · exact hc

end Smtm
