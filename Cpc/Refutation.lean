import Cpc.Spec
import Cpc.Lemmas

open Eo
open Smtm

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (forall M : SmtModel, ¬ (eo_interprets M F true)) :=
by
  sorry
