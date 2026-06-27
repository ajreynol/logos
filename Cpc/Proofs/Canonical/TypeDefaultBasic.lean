import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

/-!
Basic facts about the refactored `__smtx_type_default` (two parallel types).

Goal 1 (`type_default_notvalue_or_typed`): the default value is either `NotValue`
or a value whose type is the input type.

Goal 2 (`type_default_canonical_of_typed`): the canonicity conjunct that was
dropped from `native_inhabited_type` is implied by the typing conjunct.

The non-recursive cases are discharged here. The recursive cases (`Datatype`,
`Map`, `Set`, `Seq`) are the substance and are isolated as `sorry` with the
generalization that the induction needs spelled out below.
-/

/--
The generalization that discharges Goal 1, over the two parallel types `V`
(folded/substituted, determines the value) and `T` (driving the recursion), with the
*diagonal guard* `V = T`. Off the diagonal the claim is genuinely false in the
`Datatype` case (the value is annotated with the folded type `V`, so its type is `V`,
not the driving type `T`); the guard restricts to `V = T`, where it holds. Everything
else is independent of `V` (the matched second argument decides the value), so the
guard is just introduced and ignored.

The `Map` case relies on the new `NotValue`-guard in `__smtx_type_default_rec`'s `Map`
clause: when the element default `rec U U` is `NotValue` the whole map default is
`NotValue` (left disjunct); otherwise the `V = T` form of the IH (`ih rfl`) gives
`typeof (rec U U) = U`, hence the map is typed.

All cases are proved except `Datatype`, which is the remaining substitution-typing
kernel (the `cons_default ↔ typeof_dt_cons_value_rec` correspondence). `motive2`/
`motive3` are the datatype-helper motives, set to `True`.
-/
theorem notvalue_or_typed_rec : ∀ V T, V = T →
    __smtx_type_default_rec V T = SmtValue.NotValue ∨
    __smtx_typeof_value (__smtx_type_default_rec V T) = T := by
  refine __smtx_type_default_rec.induct
    (motive1 := fun V T => V = T →
      __smtx_type_default_rec V T = SmtValue.NotValue ∨
      __smtx_typeof_value (__smtx_type_default_rec V T) = T)
    (motive2 := fun _ _ _ _ _ => True) (motive3 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro sF dF sU dU _ heq  -- Datatype kernel: diagonal datatype default is typed
    injection heq with hs hd; subst hs; subst hd
    sorry
  · intro V _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- Bool
  · intro V _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- Int
  · intro V _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- Real
  · intro V _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- RegLan
  · intro V w _; right
    simp [__smtx_type_default_rec, __smtx_typeof_value, native_nat_to_int, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_to_nat, native_ite]  -- BitVec
  · intro V _; right
    simp [__smtx_type_default_rec, __smtx_typeof_value, native_char_valid, native_ite]  -- Char
  · intro V T U ih heq  -- Map
    rw [__smtx_type_default_rec]
    have ihU := ih rfl
    by_cases hv : native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = true
    · left; rw [native_ite, if_pos hv]
    · right; rw [native_ite, if_neg hv]
      simp only [__smtx_typeof_value, __smtx_typeof_map_value]
      rcases ihU with h0 | h1
      · exact absurd (by simp [native_veq, h0]) hv
      · rw [h1]
  · intro V T _; right
    simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]  -- Set
  · intro V T _; right
    simp [__smtx_type_default_rec, __smtx_typeof_value, __smtx_typeof_seq_value]  -- Seq
  · intro V i _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- USort
  · intro V T U _; right; simp [__smtx_type_default_rec, __smtx_typeof_value]  -- FunType
  · intro V T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 heq  -- None/TypeRef/DtcAppType
    cases T with
    | None => left; simp [__smtx_type_default_rec]
    | TypeRef s => left; simp [__smtx_type_default_rec]
    | DtcAppType A B => left; simp [__smtx_type_default_rec]
    | Datatype a b => exact (h1 a b a b heq rfl).elim
    | _ => simp_all
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue
      ∨ __smtx_typeof_value (__smtx_type_default T) = T := by
  unfold __smtx_type_default
  exact notvalue_or_typed_rec T T rfl

/--
The recursive canonicity invariant, generalized over the two parallel types `tF`,
`tU` so the structural recursion of `__smtx_type_default_rec` goes through. Stated as
*typing implies canonicity*: a default value whose computed type really is `tU` is
canonical. The typing hypothesis is exactly what makes the `Map` case go: from
`typeof (rec U U) = U` we get `default U = rec U U` for free, so the map's
`map_default_canonical` "default-entry agrees with the type's default" obligation
holds without a separate idempotence lemma.

Every non-recursive case and the `Map`/`Set`/`Seq` cases are discharged here. The
`Datatype` case (`case1`) is the remaining kernel: the datatype spine needs
*unconditional* canonicity of each field default `rec TF TU` (the typing hypothesis
on the whole value does not hand you typing of each field directly), which is the
`cons_default ↔ typeof_dt_cons_value_rec` correspondence flagged in
`default_rec_notvalue_or_typed`. It is isolated here with the `motive2`/`motive3`
helper motives set to `True`.
-/
theorem canon_rec_aux : ∀ V T,
    __smtx_typeof_value (__smtx_type_default_rec V T) = T →
    __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true := by
  refine __smtx_type_default_rec.induct
    (motive1 := fun V T => __smtx_typeof_value (__smtx_type_default_rec V T) = T →
      __smtx_value_canonical_bool (__smtx_type_default_rec V T) = true)
    (motive2 := fun _ _ _ _ _ => True) (motive3 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · sorry  -- Datatype kernel: needs the substitution-typing correspondence (see above)
  · intros; simp [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- Bool
  · intros; simp [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- Int
  · intros; simp [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- Real
  · intros
    simp [__smtx_type_default_rec, __smtx_value_canonical_bool, native_re_canonical,
          native_re_none]  -- RegLan
  · intros
    simp [__smtx_type_default_rec, __smtx_value_canonical_bool, native_nat_to_int,
          native_zleq, native_zeq, native_mod_total, native_ite]  -- BitVec
  · intros
    simp [__smtx_type_default_rec, __smtx_value_canonical_bool, native_char_valid]  -- Char
  · intro V T U ih hh  -- Map
    rw [__smtx_type_default_rec] at hh ⊢
    by_cases hv : native_veq (__smtx_type_default_rec U U) SmtValue.NotValue = true
    · -- element default is `NotValue`, so the map default is `NotValue`; `hh` is impossible
      rw [native_ite, if_pos hv] at hh
      simp only [__smtx_typeof_value] at hh
      exact absurd hh (by simp)
    · rw [native_ite, if_neg hv] at hh ⊢
      simp only [__smtx_typeof_value, __smtx_typeof_map_value] at hh
      injection hh with hT hU
      have hc := ih hU
      simp only [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical,
                 hU, hc, native_ite, native_veq, native_and, __smtx_type_default,
                 decide_true, Bool.and_true, ite_self]
  · intros
    simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_msm_get_default, native_and, native_veq,
          native_ite, __smtx_typeof_value, __smtx_type_default]  -- Set
  · intros
    simp [__smtx_type_default_rec, __smtx_value_canonical_bool, __smtx_seq_canonical]  -- Seq
  · intros; simp [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- USort
  · intros; simp [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- FunType
  · intro V T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _
    cases T <;> simp_all [__smtx_type_default_rec, __smtx_value_canonical_bool]  -- None/TypeRef/DtcAppType
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/--
Canonicity is implied by typing. Reduces (via `canon_rec_aux`) to the canonicity
invariant of the default value. All cases except `Datatype` are proved; the
`Datatype` case is the remaining kernel inside `canon_rec_aux`.
-/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  unfold __smtx_type_default at h ⊢
  apply canon_rec_aux
  unfold native_Teq at h
  exact of_decide_eq_true h

end Smtm
