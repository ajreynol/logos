module

public import Cpc.SmtModel
import all Cpc.SmtModel

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace Smtm

/-!
Basic facts about the declaration-based default generator.

The latest model refactor replaced the resolved/unresolved two-type recursion
with five mutually recursive builders over declaration tails.  The old
functional-induction proof therefore no longer applies.  Keep the remaining
semantic obligation isolated here while the new proof is reconstructed around
`__smtx_field_type_default` and declaration well-formedness.
-/

/-- Remaining semantic obligation for the refactored default generator. -/
theorem type_default_kernel (T : SmtType) :
    (__smtx_type_default T = SmtValue.NotValue ∨
      __smtx_typeof_value (__smtx_type_default T) = T) ∧
    (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true →
      __smtx_value_canonical_bool (__smtx_type_default T) = true) := by
  sorry

/-- A default is either unavailable or has the requested type. -/
theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue ∨
      __smtx_typeof_value (__smtx_type_default T) = T :=
  (type_default_kernel T).1

/-- A well-typed default value is canonical. -/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true :=
  (type_default_kernel T).2 h

end Smtm
