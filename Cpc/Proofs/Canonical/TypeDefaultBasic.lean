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
  | BitVec w => sorry
  | Char => sorry
  | Datatype s d => sorry
  | Map A B => sorry
  | Set A => sorry
  | Seq A => sorry

/--
Canonicity is implied by typing. Reduces to a canonicity invariant of the default
value; for the datatype spine canonicity is unconditional (every field default is
canonical), while the `Map`/`Set`/`Seq` cases genuinely use the typing hypothesis.
-/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  sorry

end Smtm
