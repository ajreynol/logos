import Cpc.Parser
import Cpc.Api

/-!
The `logos` executable: read a CPC proof in s-expression syntax, and report
whether it is a refutation whose soundness `Cpc/ApiCorrect.lean` establishes.

The three calls below are exactly the three hypotheses of
`correct___logos_check_refutation` (`Cpc/ApiCorrect.lean`), which is
`correct___eo_is_refutation` (`Cpc/Proofs/Checker.lean`) restated about them:

* `Eo.logos_check_refutation assums cmds` -- Logos runs `cmds` from the
  assumptions and ends in a closed state that has proven `false`;
* `Eo.logos_check_translatableAssumptionList assums` and
  `Eo.logos_check_cmdListTranslationOk cmds` -- every assumption, and every rule
  argument the rule proofs interpret, has an SMT-LIB counterpart under
  `Cpc/SmtModel.lean`.

So `correct` here means: the conjunction of this file's `assume`d formulas,
namely `Eo.logos_assumption_term assums`, is unsatisfiable.  When Logos accepts
the proof but a side condition fails, the run is reported as `unsupported`
instead: the proof is a valid CPC derivation, but it mentions something the
specification does not model, so the soundness theorem says nothing about it.
-/

/-- Verdicts, kept in one place so the exit status and the printed word cannot drift. -/
inductive Verdict where
  /-- Checked, and covered by `correct___logos_check_refutation`. -/
  | correct
  /-- Logos did not accept the proof. -/
  | incorrect
  /-- Logos accepted the proof, but it is outside the specification's fragment. -/
  | unsupported

def Verdict.word : Verdict -> String
  | .correct => "correct"
  | .incorrect => "incorrect"
  | .unsupported => "unsupported"

def Verdict.status : Verdict -> UInt32
  | .correct => 0
  | .incorrect => 1
  | .unsupported => 2

/--
Report a verdict: the detail goes to stderr first and is flushed, so that a
caller merging the two streams still sees the verdict as the final line.
-/
def report (verdict : Verdict) (detail : String := "") : IO UInt32 := do
  if !detail.isEmpty then
    let err ← IO.getStderr
    err.putStrLn detail
    err.flush
  let out ← IO.getStdout
  out.putStrLn verdict.word
  out.flush
  return verdict.status

/-- Keep diagnostics readable when the offending term is large. -/
def abbreviate (s : String) : String :=
  if s.length ≤ 400 then s else String.ofList (s.toList.take 400) ++ " ..."

def checkProof (path : String) : IO UInt32 := do
  let proof ← IO.FS.readFile path
  match Eo.parseProof proof with
  | .ok (assums, cmds) =>
    if !Eo.logos_check_refutation assums cmds then
      report .incorrect
    else if !Eo.logos_check_translatableAssumptionList assums then
      -- The refutation stands as a CPC derivation, but `TranslatableAssumptionList`
      -- fails, so `correct___logos_check_refutation` does not apply to it.
      let detail :=
        match Eo.logos_untranslatable_assumption assums with
        | some (i, A) =>
          s!"Error: assumption {i} has no SMT-LIB translation, so this proof is \
             outside the fragment the correctness theorem covers:\n  \
             {abbreviate (toString (repr A))}"
        | none => "Error: an assumption has no SMT-LIB translation."
      report .unsupported detail
    else if !Eo.logos_check_cmdListTranslationOk cmds then
      -- Likewise for `CmdListTranslationOk`.
      let detail :=
        match Eo.logos_untranslatable_cmd cmds with
        | some (i, c) =>
          s!"Error: the arguments of command {i} have no SMT-LIB translation, so this \
             proof is outside the fragment the correctness theorem covers:\n  \
             {abbreviate (toString (repr c))}"
        | none => "Error: a command argument has no SMT-LIB translation."
      report .unsupported detail
    else
      report .correct
  | .error err =>
    IO.eprintln s!"Error parsing proof: {err}"
    return 1

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: logos <path-to-proof-file>"
      return 1
  checkProof path

-- To build, run "lake build logos" in this directory.
-- To run, use "lake exe logos <path-to-proof-file>".
