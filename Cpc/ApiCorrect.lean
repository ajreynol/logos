module

public import Cpc.ApiChecks
import all Cpc.ApiChecks
public import Cpc.Proofs.Checker
import all Cpc.Proofs.Checker

public section

/-!
# Soundness of the executable, stated about what the executable computes

`correct___eo_is_refutation` (`Cpc/Proofs/Checker.lean`) is stated about an
assumption term `F`, a `CCmdList`, and two side conditions.  The theorem below
is the same statement with every one of those replaced by the runtime check that
computes it, so it applies directly to the expression `Main.lean` evaluates:

```
Eo.logos_check_refutation assums cmds
  && Eo.logos_check_translatableAssumptionList assums
  && Eo.logos_check_cmdListTranslationOk cmds
```

When `logos` prints `correct`, all three of those checks returned `true` on the
parsed proof, so by this theorem the conjunction of that proof's assumptions --
`Eo.logos_assumption_term assums` -- is unsatisfiable.  Nothing else about the
run has to be argued informally.

What remains outside the theorem: the s-expression reader and parser
(`Logos/Parser.lean`, `Cpc/Parser.lean`) are unverified, so `assums` is whatever
they read out of the file, and `logos` does not compare the file's assumptions
against an original input problem (`include` and `reference` commands are
ignored).  The Lean-native front end (`MainNative.lean`) is also not covered: it
runs `#eval` scripts that call the generated, unguarded `Eo.logos_invoke_assume`.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of the `logos` executable's verdict.

Each hypothesis is a `Bool` the executable computes with no proof obligation left
to the caller:

* `logos_check_translatableAssumptionList assums` gives
  `TranslatableAssumptionList (logos_assumption_term assums)`,
* `logos_check_cmdListTranslationOk cmds` gives `CmdListTranslationOk cmds`,
* `logos_check_refutation assums cmds` gives
  `eo_is_refutation (logos_assumption_term assums) cmds`,

and `correct___eo_is_refutation` turns the three into unsatisfiability of the
proof's assumptions.
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
