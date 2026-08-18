module

public import CpcMini.ApiChecks
import all CpcMini.ApiChecks
public import CpcMini.Proofs.Checker
import all CpcMini.Proofs.Checker

public section

/-!
# Soundness of the executable, stated about what the executable computes

The CpcMini counterpart of `Cpc/ApiCorrect.lean`: `correct___eo_is_refutation`
restated with each of its hypotheses replaced by the runtime check that computes
it, so that it applies directly to the expression `MainMini.lean` evaluates.

The unverified remainder is the same as for CPC: the s-expression reader and
parser, the fact that Logos does not compare a proof's assumptions against an
original input problem, and the Lean-native front end, which still calls the
generated, unguarded `Eo.logos_invoke_assume`.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of the `logos-mini` executable's verdict: if all three checks return
`true`, the conjunction of the proof's assumptions is unsatisfiable.
-/
theorem correct___logos_check_refutation (assums : List Term) (cmds : CCmdList) :
  logos_check_translatableAssumptionList assums = true ->
  logos_check_cmdListTranslationOk cmds = true ->
  logos_check_refutation assums cmds = true ->
  eo_satisfiability (logos_assumption_term assums) false :=
by
  intro hAssums hCmds hRefutation
  exact correct___eo_is_refutation (logos_assumption_term assums) cmds
    (translatableAssumptionList_of_check assums hAssums)
    (cmdListTranslationOk_of_check cmds hCmds)
    (eo_is_refutation_of_check assums cmds hRefutation)
