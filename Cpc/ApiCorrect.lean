module

public import Cpc.ApiChecks
import all Cpc.ApiChecks
public import Cpc.Proofs.Checker
import all Cpc.Proofs.Checker

public section

/-!
# Soundness of the `logos` executable

`correct___eo_is_refutation` (`Cpc/Proofs/Checker.lean`) is stated about an
assumption term `F`, a `CCmdList`, and two side conditions.  The theorems below
restate it about what the executable actually runs:
`Eo.logos_check_proof` (`Cpc/Api.lean`), which takes the text of a proof file to
the word `logos` prints for it.

* `correct___logos_verdict` is about the verdict of a parsed proof.
* `correct___logos_check_proof` is about the file's text, and phrases the
  conclusion in terms of the parser's assumption list: every model makes one of
  those assumptions false.

Reading the theorem as a statement about a proof file therefore requires only
one thing beyond it: that `Cpc/Parser.lean` read the intended assumptions out of
the file.  That is what stays unverified -- the s-expression reader and parser
have no correctness proof, and `logos` does not compare a proof's assumptions
against an original input problem (`include` and `reference` commands are
ignored).  The Lean-native front end (`MainNative.lean`) is not covered either:
it runs `#eval` scripts that call the generated, unguarded
`Eo.logos_invoke_assume`.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of the verdict `Main.lean` computes: `correct` for a parsed proof means
the conjunction of its assumptions is unsatisfiable.

Each of the three checks `logos_verdict` runs discharges one hypothesis of
`correct___eo_is_refutation`, with no proof obligation left to the caller:

* `logos_check_translatableAssumptionList assums` gives
  `TranslatableAssumptionList (logos_assumption_term assums)`,
* `logos_check_cmdListTranslationOk cmds` gives `CmdListTranslationOk cmds`,
* `logos_check_refutation assums cmds` gives
  `eo_is_refutation (logos_assumption_term assums) cmds`.
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
Soundness of the `logos` executable, stated about the proof file it reads.

If the parser reads the assumptions `assums` (and the commands `cmds`) out of
`input`, and `logos` prints `correct` for `input`, then every total typed SMT
model makes at least one of those assumptions false -- the assumptions have no
common model.
-/
theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
    (hParse : parseProof input = Except.ok (assums, cmds))
    (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
    ∀ M : SmtModel, model_total_typed M ->
      ∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
  intro M hM
  have hVerdict : logos_verdict assums cmds = Verdict.correct := by
    rw [logos_check_proof_of_parse input assums cmds hParse] at hCorrect
    exact Except.ok.inj hCorrect
  cases correct___logos_verdict assums cmds hVerdict with
  | intro_false hFalse => exact exists_false_assumption M assums (hFalse M hM)
