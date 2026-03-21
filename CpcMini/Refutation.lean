import CpcMini.Spec
import CpcMini.Lemmas

open Eo
open Smtm

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (eo_interprets F false) :=
by
  sorry
