module

public import Cpc.ApiChecks
import all Cpc.ApiChecks
public import Cpc.ApiNative
import all Cpc.ApiNative
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
* `correct___logos_check_proof` is about the file's text: if `logos` prints
  `correct` for it, the assumptions the parser read out of it are unsatisfiable.

Reading the theorem as a statement about a proof file therefore requires only
one thing beyond it: that `Cpc/Parser.lean` read the intended assumptions out of
the file.  That is what stays unverified -- the s-expression reader and parser
have no correctness proof, and `logos` does not compare a proof's assumptions
against an original input problem (`include` and `reference` commands are
ignored).

`correct___logos_native_verdict` is the same statement for the Lean-native front
end (`MainNative.lean`, `Cpc/ApiNative.lean`), whose scripts name their
assumptions and commands directly instead of parsing them.  What is unverified
there is the counterpart of the parser: nothing checks that a script builds its
state the way `Eo.logos_native_run` does.  A script that calls the generated,
unguarded `Eo.logos_invoke_assume` of `Cpc/Logos.lean` is covered by neither
theorem.
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
`input`, and `logos` prints `correct` for `input`, then the conjunction of those
assumptions is unsatisfiable.
-/
theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
    (hParse : parseProof input = Except.ok (assums, cmds))
    (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
    eo_satisfiability (logos_assumption_term assums) false := by
  apply correct___logos_verdict assums cmds
  rw [logos_check_proof_of_parse input assums cmds hParse] at hCorrect
  exact Except.ok.inj hCorrect

/--
Soundness of the `logos-native` executable, stated about the script it reads.

A Lean-native proof script builds a `NativeState` from `logos_native_init_state`
by a sequence of `logos_native_invoke_assume` calls followed by a sequence of
`logos_native_invoke_cmd` calls, which is `Eo.logos_native_run assums cmds` for
the assumptions and commands it names; `logos-native` prints the value of the
`logos_native_state_is_refutation` the script evaluates.  So a `true` from such a
script means the conjunction of the assumptions it names is unsatisfiable --
exactly what `correct` from `logos` means for the assumptions its parser read.

`logos_native_verdict_eq_verdict` (`Cpc/ApiNative.lean`) is what makes this the
same theorem: a script of that shape computes `logos_verdict` of its own
assumptions and commands, so the three checks are discharged there.
-/
theorem correct___logos_native_verdict (assums : List Term) (cmds : CCmdList)
    (h : logos_native_state_is_refutation (logos_native_run assums cmds) = true) :
    eo_satisfiability (logos_assumption_term assums) false := by
  apply correct___logos_verdict assums cmds
  rw [← logos_native_verdict_eq_verdict assums cmds]
  exact (logos_native_state_is_refutation_eq_correct _).mp h
