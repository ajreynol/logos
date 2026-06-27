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
The crux generalization for the `Datatype` case. `__smtx_type_default_rec` runs on
two types: `tF` (the substituted/folded type, which determines the value and its
annotations) and `tU` (the original unsubstituted type, which drives the structural
recursion). The result, when it is a value, has type `tF`.

This is only true when `tF` and `tU` are *substitution-related* (`tF` is `tU` with
recursive `TypeRef`s replaced by their `Datatype` unfolding); for unrelated
`(tF, tU)` it is false (e.g. `rec Bool Int = Numeral 0 : Int ≠ Bool`). Stating that
relation and threading it (together with the `cons_default ↔
typeof_dt_cons_value_rec` correspondence) is the remaining work.
-/
theorem default_rec_notvalue_or_typed (tU tF : SmtType) :
    __smtx_type_default_rec tF tU = SmtValue.NotValue
      ∨ __smtx_typeof_value (__smtx_type_default_rec tF tU) = tF := by
  sorry

theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue
      ∨ __smtx_typeof_value (__smtx_type_default T) = T := by
  cases T with
  | Bool => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | Int => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | Real => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | RegLan => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | USort i => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | FunType A B => right; simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value]
  | None => left; simp [__smtx_type_default, __smtx_type_default_rec]
  | TypeRef s => left; simp [__smtx_type_default, __smtx_type_default_rec]
  | DtcAppType A B => left; simp [__smtx_type_default, __smtx_type_default_rec]
  | BitVec w =>
    right
    simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value,
          native_nat_to_int, native_and, native_zleq, native_zeq, native_mod_total,
          native_int_to_nat, native_ite]
  | Char =>
    right
    simp [__smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value,
          native_char_valid, native_ite]
  | Datatype s d => sorry
  | Map A B => sorry
  | Set A => sorry
  | Seq A => sorry

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
    simp only [__smtx_typeof_value, __smtx_typeof_map_value] at hh
    injection hh with hT hU
    have hc := ih hU
    simp only [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical,
               hU, hc, native_ite, native_and, native_veq, __smtx_type_default,
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
