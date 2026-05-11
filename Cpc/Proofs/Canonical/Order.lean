import Cpc.Proofs.Canonical.Basic

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/--
Temporary law assumption for the strict order induced by `native_vcmp`.

The generated `Ord SmtValue` comparator is executable but opaque to Lean, so we
record the trichotomy fragment needed by canonical map update here until the
order is made proof-transparent.
-/
theorem native_vcmp_flip
    {a b : SmtValue}
    (hNe : native_veq a b = false)
    (hCmp : native_vcmp a b = false) :
    native_vcmp b a = true := by
  sorry

/--
Temporary irreflexivity/disequality assumption for the strict order induced by
`native_vcmp`.
-/
theorem native_vcmp_ne
    {a b : SmtValue}
    (hCmp : native_vcmp a b = true) :
    native_veq a b = false := by
  sorry

/--
Temporary transitivity assumption for the strict order induced by
`native_vcmp`.
-/
theorem native_vcmp_trans
    {a b c : SmtValue}
    (hab : native_vcmp a b = true)
    (hbc : native_vcmp b c = true) :
    native_vcmp a c = true := by
  sorry

end Smtm
