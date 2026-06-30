import Cpc.SmtModel
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm

/-!
Basic facts about the refactored `__smtx_type_default` (two parallel types `V`/`T`,
via `__smtx_type_default_rec`).

* `type_default_notvalue_or_typed` (Goal 1): the default value is either `NotValue`
  or a value whose type is the input type.
* `type_default_canonical_of_typed` (Goal 2): the default value is canonical.

Both reduce to the diagonal instance of the combined kernel `datatype_kernel_rec`,
which is proved by the functional induction `__smtx_type_default_rec.induct` over the
three mutually-recursive default builders. The substantive content is the `Datatype`
case, threaded through the substitution-closure relations `SubstStar` / `DtSubstStar`
/ `DtcSubstStar` / `FieldRel` (closed under the composed substitutions that arise for
mutually-recursive datatypes), the `chainType` ↔ `typeof_dt_cons_value_rec`
correspondence, and the constructor-position bookkeeping (`drop_cons`).
-/

-- `FieldRel TF TU`: either substitution-related, or TU forces NotValue regardless of first arg.
mutual
inductive SubstStar : SmtType → SmtType → Prop where
  | refl (T : SmtType) : SubstStar T T
  | dt {sF sU : native_String} {dF dU : SmtDatatype} :
      DtSubstStar dF dU → SubstStar (SmtType.Datatype sF dF) (SmtType.Datatype sU dU)
inductive FieldRel : SmtType → SmtType → Prop where
  | rel {TF TU : SmtType} : SubstStar TF TU → FieldRel TF TU
  | forcesNV {TF TU : SmtType} :
      (∀ V, __smtx_type_default_rec V TU = SmtValue.NotValue) → FieldRel TF TU
inductive DtcSubstStar : SmtDatatypeCons → SmtDatatypeCons → Prop where
  | unit : DtcSubstStar SmtDatatypeCons.unit SmtDatatypeCons.unit
  | cons {TF TU : SmtType} {cF cU : SmtDatatypeCons} :
      FieldRel TF TU → DtcSubstStar cF cU →
      DtcSubstStar (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons TU cU)
inductive DtSubstStar : SmtDatatype → SmtDatatype → Prop where
  | null : DtSubstStar SmtDatatype.null SmtDatatype.null
  | sum {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype} :
      DtcSubstStar cF cU → DtSubstStar dF dU →
      DtSubstStar (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU)
end

theorem dtcSubstStar_refl : ∀ c : SmtDatatypeCons, DtcSubstStar c c
  | SmtDatatypeCons.unit => DtcSubstStar.unit
  | SmtDatatypeCons.cons T c => DtcSubstStar.cons (FieldRel.rel (SubstStar.refl T)) (dtcSubstStar_refl c)

theorem dtSubstStar_refl : ∀ D : SmtDatatype, DtSubstStar D D
  | SmtDatatype.null => DtSubstStar.null
  | SmtDatatype.sum c D => DtSubstStar.sum (dtcSubstStar_refl c) (dtSubstStar_refl D)

-- TypeRef as 2nd arg forces NotValue
theorem rec_typeref_nv (s2 : native_String) (V : SmtType) :
    __smtx_type_default_rec V (SmtType.TypeRef s2) = SmtValue.NotValue := by
  simp [__smtx_type_default_rec]

mutual
theorem fieldRel_of_type_subst (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType, FieldRel (__smtx_type_substitute s d T) T
  | SmtType.Datatype s2 d2 => by
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s s2 = true
      · rw [native_ite, if_pos hEq]; exact FieldRel.rel (SubstStar.dt (dtSubstStar_refl d2))
      · rw [native_ite, if_neg hEq]; exact FieldRel.rel (SubstStar.dt (dtSubstStar_of_subst s _ d2))
  | SmtType.TypeRef s2 => FieldRel.forcesNV (fun V => rec_typeref_nv s2 V)
  | SmtType.None => FieldRel.rel (SubstStar.refl _)
  | SmtType.Bool => FieldRel.rel (SubstStar.refl _)
  | SmtType.Int => FieldRel.rel (SubstStar.refl _)
  | SmtType.Real => FieldRel.rel (SubstStar.refl _)
  | SmtType.RegLan => FieldRel.rel (SubstStar.refl _)
  | SmtType.BitVec w => FieldRel.rel (SubstStar.refl _)
  | SmtType.Map A B => FieldRel.rel (SubstStar.refl _)
  | SmtType.Set A => FieldRel.rel (SubstStar.refl _)
  | SmtType.Seq A => FieldRel.rel (SubstStar.refl _)
  | SmtType.Char => FieldRel.rel (SubstStar.refl _)
  | SmtType.USort i => FieldRel.rel (SubstStar.refl _)
  | SmtType.FunType A B => FieldRel.rel (SubstStar.refl _)
  | SmtType.DtcAppType A B => FieldRel.rel (SubstStar.refl _)

theorem dtcSubstStar_of_subst (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons, DtcSubstStar (__smtx_dtc_substitute s d c) c
  | SmtDatatypeCons.unit => by simpa [__smtx_dtc_substitute] using DtcSubstStar.unit
  | SmtDatatypeCons.cons T c => by
      simpa [__smtx_dtc_substitute] using
        DtcSubstStar.cons (fieldRel_of_type_subst s d T) (dtcSubstStar_of_subst s d c)

theorem dtSubstStar_of_subst (s : native_String) (d : SmtDatatype) :
    ∀ D : SmtDatatype, DtSubstStar (__smtx_dt_substitute s d D) D
  | SmtDatatype.null => by simpa [__smtx_dt_substitute] using DtSubstStar.null
  | SmtDatatype.sum c D => by
      simpa [__smtx_dt_substitute] using
        DtSubstStar.sum (dtcSubstStar_of_subst s d c) (dtSubstStar_of_subst s d D)
end

-- Composition: the relations are preserved under substituting the folded side.
mutual
theorem fieldRel_subst (s : native_String) (d : SmtDatatype) {TF TU : SmtType}
    (h : FieldRel TF TU) : FieldRel (__smtx_type_substitute s d TF) TU := by
  cases h with
  | rel hss =>
    cases hss with
    | refl => exact fieldRel_of_type_subst s d _
    | @dt sF sU dF dU hdt =>
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s sF = true
      · rw [native_ite, if_pos hEq]; exact FieldRel.rel (SubstStar.dt hdt)
      · rw [native_ite, if_neg hEq]
        exact FieldRel.rel (SubstStar.dt (dtSubstStar_subst s (__smtx_dt_lift sF dF d) hdt))
  | forcesNV hnv => exact FieldRel.forcesNV hnv

theorem dtcSubstStar_subst (s : native_String) (d : SmtDatatype) {cF cU : SmtDatatypeCons}
    (h : DtcSubstStar cF cU) : DtcSubstStar (__smtx_dtc_substitute s d cF) cU := by
  cases h with
  | unit => simpa [__smtx_dtc_substitute] using DtcSubstStar.unit
  | @cons TF TU cF cU hfr hc =>
      simpa [__smtx_dtc_substitute] using
        DtcSubstStar.cons (fieldRel_subst s d hfr) (dtcSubstStar_subst s d hc)

theorem dtSubstStar_subst (s : native_String) (d : SmtDatatype) {dF dU : SmtDatatype}
    (h : DtSubstStar dF dU) : DtSubstStar (__smtx_dt_substitute s d dF) dU := by
  cases h with
  | null => simpa [__smtx_dt_substitute] using DtSubstStar.null
  | @sum cF cU dF dU hc hd =>
      simpa [__smtx_dt_substitute] using
        DtSubstStar.sum (dtcSubstStar_subst s d hc) (dtSubstStar_subst s d hd)
end

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

theorem datatype_kernel_rec : ∀ V T : SmtType,
    SubstStar V T →
    __smtx_type_default_rec V T = SmtValue.NotValue ∨
    (__smtx_typeof_value (__smtx_type_default_rec V T) = V ∧
     __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true) := by
  refine __smtx_type_default_rec.induct
    (motive1 := fun V T => SubstStar V T →
      __smtx_type_default_rec V T = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_type_default_rec V T) = V ∧
       __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true))
    (motive2 := fun s d n DF DU =>
      DtSubstStar DF DU → DF = drop_cons (__smtx_dt_substitute s d d) n →
      __smtx_datatype_default s d n DF DU = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_datatype_default s d n DF DU) = SmtType.Datatype s d ∧
       __smtx_value_canonical_bool (__smtx_datatype_default s d n DF DU) = true))
    (motive3 := fun v cF cU =>
      ∀ base, DtcSubstStar cF cU → __smtx_typeof_value v = chainType cF base →
      __smtx_value_canonical_bool v = true →
      __smtx_datatype_cons_default v cF cU = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_datatype_cons_default v cF cU) = base ∧
       __smtx_value_canonical_bool (__smtx_datatype_cons_default v cF cU) = true))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro sF dF sU dU ih2 hss
    rw [__smtx_type_default_rec]
    have hdt : DtSubstStar dF dU := by
      cases hss with
      | refl => exact dtSubstStar_refl dF
      | dt h => exact h
    exact ih2 (dtSubstStar_subst sF dF hdt) (drop_cons_zero _).symm
  · intro V hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_re_canonical, native_re_none]
  · intro V w hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_nat_to_int, native_and, native_zleq, native_zeq, native_mod_total, native_int_to_nat, native_ite]
  · intro V hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool, native_char_valid, native_ite]
  · intro V T U ih hss
    cases hss with
    | refl =>
      rw [__smtx_type_default_rec]
      by_cases hv : native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = true
      · left; rw [native_ite, if_pos hv]
      · rw [native_ite, if_neg hv]
        rcases ih (SubstStar.refl U) with h0 | ⟨h1, h2⟩
        · exact absurd (by simp [native_veq, h0]) hv
        · right; refine ⟨?_, ?_⟩
          · simp [__smtx_typeof_value, __smtx_typeof_map_value, h1]
          · simp [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical, h1, h2, native_veq, native_and, native_ite, __smtx_type_default, decide_true, Bool.and_true, ite_self]
  · intro V T hss
    cases hss with
    | refl =>
      right; refine ⟨?_, ?_⟩
      · simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]
      · simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical, __smtx_msm_get_default, native_and, native_veq, native_ite, __smtx_typeof_value, __smtx_type_default]
  · intro V T hss
    cases hss with
    | refl =>
      right; refine ⟨?_, ?_⟩
      · simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_seq_value]
      · simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_seq_canonical]
  · intro V i hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V T U hss; cases hss with | refl => right; refine ⟨?_, ?_⟩ <;> simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro V T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hss
    left
    cases T with
    | None => simp [__smtx_type_default_rec]
    | TypeRef s => simp [__smtx_type_default_rec]
    | DtcAppType A B => simp [__smtx_type_default_rec]
    | Datatype a b =>
        cases hss with
        | refl => exact (h1 a b a b rfl rfl).elim
        | @dt sF sU dF dU hdt => exact (h1 sF dF a b rfl rfl).elim
    | _ => simp_all
  · intro s d n cF dF cU dU ih3 ih2 hdt hdrop
    have hcons : DtcSubstStar cF cU := by cases hdt with | sum hc _ => exact hc
    have hdtail : DtSubstStar dF dU := by cases hdt with | sum _ hd => exact hd
    have htypeofDtCons : __smtx_typeof_value (SmtValue.DtCons s d n) = chainType cF (SmtType.Datatype s d) := by
      simp only [__smtx_typeof_value]
      exact drop_lemma (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n cF dF hdrop.symm
    have hcanonDtCons : __smtx_value_canonical_bool (SmtValue.DtCons s d n) = true := by
      simp [__smtx_value_canonical_bool]
    have hdrop' : dF = drop_cons (__smtx_dt_substitute s d d) (Nat.succ n) := by
      rw [drop_cons_succ, ← hdrop]
    rw [__smtx_datatype_default]
    simp only [native_not, native_veq, native_ite]
    split
    · next hcond =>
      rcases ih3 (SmtType.Datatype s d) hcons htypeofDtCons hcanonDtCons with hNV | hTy
      · rw [hNV] at hcond; simp at hcond
      · right; exact hTy
    · next hcond =>
      rcases ih3 (SmtType.Datatype s d) hcons htypeofDtCons hcanonDtCons with hNV | hTy
      · exact ih2 hdtail hdrop'
      · exfalso
        have hv0ne : __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU ≠ SmtValue.NotValue := by
          intro hc; rw [hc] at hTy; simp [__smtx_typeof_value] at hTy
        simp [hv0ne] at hcond
  · intro s d n dF dU hne hdt hdrop
    left
    cases hdt with
    | null => simp [__smtx_datatype_default]
    | @sum cF cU dF' dU' hc hd => exact (hne cF dF' cU dU' rfl rfl).elim
  · intro v base hc htypeof hcanon
    right
    refine ⟨?_, ?_⟩
    · simpa [__smtx_datatype_cons_default, chainType] using htypeof
    · simpa [__smtx_datatype_cons_default] using hcanon
  · intro v TF cF TU cU _v0 ih1 ih3 base hc htypeof hcanon
    have hfr : FieldRel TF TU := by cases hc with | cons hf _ => exact hf
    have hcF : DtcSubstStar cF cU := by cases hc with | cons _ h => exact h
    rw [__smtx_datatype_cons_default]
    by_cases hv : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true
    · left; rw [native_ite, if_pos hv]
    · rw [native_ite, if_neg hv]
      have hss : SubstStar TF TU := by
        cases hfr with
        | rel h => exact h
        | forcesNV h => exact absurd (by simp [native_veq, h TF]) hv
      rcases ih1 hss with hNV | ⟨hTy, hCanonField⟩
      · exact absurd (by simp [native_veq, hNV]) hv
      · have hTFne : TF ≠ SmtType.None := by
          cases hss with
          | refl => intro hNone; rw [hNone] at hv; simp [__smtx_type_default_rec, native_veq] at hv
          | dt _ => intro hNone; cases hNone
        have htypeofApply : __smtx_typeof_value (SmtValue.Apply v (__smtx_type_default_rec TF TU)) = chainType cF base := by
          have hchain : chainType (SmtDatatypeCons.cons TF cF) base = SmtType.DtcAppType TF (chainType cF base) := rfl
          rw [hchain] at htypeof
          simp only [__smtx_typeof_value, htypeof, hTy, __smtx_typeof_apply_value,
                     __smtx_typeof_guard, native_Teq, native_ite, decide_true, if_true]
          simp [hTFne]
        have hcanonApply : __smtx_value_canonical_bool (SmtValue.Apply v (__smtx_type_default_rec TF TU)) = true := by
          simp [__smtx_value_canonical_bool, hcanon, hCanonField, native_and]
        exact ih3 base hcF htypeofApply hcanonApply
  · intro v cF cU hne1 hne2 base hc htypeof hcanon
    left
    cases hc with
    | unit => exact (hne1 rfl rfl).elim
    | @cons TF TU cF' cU' hf hcc => exact (hne2 TF cF' TU cU' rfl rfl).elim

/-- Diagonal instance of the kernel: the default value of any type is either
`NotValue`, or a canonical value whose type is the input type. -/
theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue
      ∨ __smtx_typeof_value (__smtx_type_default T) = T := by
  unfold __smtx_type_default
  rcases datatype_kernel_rec T T (SubstStar.refl T) with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Canonicity of the default value. The kernel makes this unconditional, so the
typing hypothesis `h` is not needed (kept for the original interface). -/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  unfold __smtx_type_default
  rcases datatype_kernel_rec T T (SubstStar.refl T) with h0 | ⟨_, hc⟩
  · rw [h0]; simp [__smtx_value_canonical_bool]
  · exact hc

end Smtm
