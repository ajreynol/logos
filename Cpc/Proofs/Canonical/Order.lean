module

public import Cpc.Proofs.Canonical.Basic
import all Cpc.Proofs.Canonical.Basic
public import Cpc.Proofs.SmtValueOrder
import all Cpc.Proofs.SmtValueOrder

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Trichotomy for the strict value order used by `native_vcmp`. -/
theorem native_vcmp_flip
    {a b : SmtValue}
    (hNe : native_veq a b = false)
    (hCmp : native_vcmp a b = false) :
    native_vcmp b a = true := by
  apply SmtValueOrder.lt_flip
  · simpa [native_veq] using hNe
  · simpa [native_vcmp] using hCmp

/-- Strictly ordered values are distinct. -/
theorem native_vcmp_ne
    {a b : SmtValue}
    (hCmp : native_vcmp a b = true) :
    native_veq a b = false := by
  have hNe : a ≠ b := SmtValueOrder.lt_ne (by simpa [native_vcmp] using hCmp)
  simpa [native_veq] using hNe

/-- Transitivity of the strict value order used by `native_vcmp`. -/
theorem native_vcmp_trans
    {a b c : SmtValue}
    (hab : native_vcmp a b = true)
    (hbc : native_vcmp b c = true) :
    native_vcmp a c = true := by
  apply SmtValueOrder.lt_trans
  · simpa [native_vcmp] using hab
  · simpa [native_vcmp] using hbc

end Smtm
