module

public import CpcMini.ApiChecks
import all CpcMini.ApiChecks
public import CpcMini.Proofs.Checker
import all CpcMini.Proofs.Checker

public section

/-!
# Soundness of the CpcMini verdict

The CpcMini counterpart of `Cpc/ApiCorrect.lean`, stated about
`Eo.logos_verdict`, the three checks of `CpcMini/Api.lean` run on a proof.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of the verdict: `correct` for a proof means the conjunction of its
assumptions is unsatisfiable.
-/
theorem correct___logos_verdict (assums : List Term) (cmds : CCmdList)
    (h : logos_verdict assums cmds = Verdict.correct) :
    eo_satisfiability (logos_assumption_term assums) false := by
  obtain ⟨hRefutation, hAssums, hCmds⟩ := checks_of_verdict_correct assums cmds h
  exact correct___eo_is_refutation (logos_assumption_term assums) cmds
    (translatableAssumptionList_of_check assums hAssums)
    (cmdListTranslationOk_of_check cmds hCmds)
    (eo_is_refutation_of_check assums cmds hRefutation)
