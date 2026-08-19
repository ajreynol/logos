module

public import CpcMini.ApiChecks
import all CpcMini.ApiChecks
public import CpcMini.Proofs.Checker
import all CpcMini.Proofs.Checker

public section

/-!
# Soundness of the `logos-mini` executable

The CpcMini counterpart of `Cpc/ApiCorrect.lean`, stated about
`Eo.logos_check_proof`, which is what `MainMini.lean` runs on a proof file.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of the verdict: `correct` on a parsed proof means the conjunction of
its assumptions is unsatisfiable.
-/
theorem correct___logos_verdict (assums : List Term) (cmds : CCmdList)
    (h : logos_verdict assums cmds = Verdict.correct) :
    eo_satisfiability (logos_assumption_term assums) false := by
  obtain ⟨hRefutation, hAssums, hCmds⟩ := checks_of_verdict_correct assums cmds h
  exact correct___eo_is_refutation (logos_assumption_term assums) cmds
    (translatableAssumptionList_of_check assums hAssums)
    (cmdListTranslationOk_of_check cmds hCmds)
    (eo_is_refutation_of_check assums cmds hRefutation)

/--
Soundness of the `logos-mini` executable, stated about the proof file it reads:
if the parser reads the assumptions `assums` out of `input` and the executable
reports `correct`, the conjunction of those assumptions is unsatisfiable.
-/
theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
    (hParse : parseProof input = Except.ok (assums, cmds))
    (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
    eo_satisfiability (logos_assumption_term assums) false := by
  apply correct___logos_verdict assums cmds
  rw [logos_check_proof_of_parse input assums cmds hParse] at hCorrect
  exact Except.ok.inj hCorrect
