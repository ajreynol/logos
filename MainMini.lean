import CpcMini.Api

/-!
The `logos-mini` executable: the CpcMini counterpart of `Main.lean`, with the
same output convention and the same correspondence to the correctness theorem.

Reading the file aside, all of the work is `Eo.logos_check_proof`
(`CpcMini/Api.lean`), and `correct___logos_check_proof`
(`CpcMini/ApiCorrect.lean`) is stated about that function: if it returns
`correct` for the contents of a file, then in every model one of the assumptions
the parser read out of that file is false.  The verdict is computed here in the
two steps `Eo.logos_check_proof` is defined as, so that the `incomplete` case
can say which assumption or command was at fault.
-/

open Eo

def Eo.Verdict.word : Verdict -> String
  | .correct => "correct"
  | .incorrect => "incorrect"
  | .incomplete => "incomplete"

def Eo.Verdict.status : Verdict -> UInt32
  | .correct => 0
  | .incorrect => 1
  | .incomplete => 2

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

/--
Why a proof Logos accepted is nevertheless outside the fragment the correctness
theorem covers: the first assumption or command that fails its side condition.
-/
def incompleteDetail (assums : List Term) (cmds : CCmdList) : String :=
  match Eo.logos_untranslatable_assumption assums with
  | some (i, A) =>
    s!"Error: assumption {i} has no SMT-LIB translation, so this proof is \
       outside the fragment the correctness theorem covers:\n  \
       {abbreviate (toString (repr A))}"
  | none =>
    match Eo.logos_untranslatable_cmd cmds with
    | some (i, c) =>
      s!"Error: the arguments of command {i} have no SMT-LIB translation, so this \
         proof is outside the fragment the correctness theorem covers:\n  \
         {abbreviate (toString (repr c))}"
    | none => "Error: a translation side condition failed."

def checkProof (path : String) : IO UInt32 := do
  let proof ← IO.FS.readFile path
  match Eo.parseProof proof with
  | .ok (assums, cmds) =>
    -- `Eo.logos_check_proof proof = .ok (Eo.logos_verdict assums cmds)`, by
    -- `Eo.logos_check_proof_of_parse` (`CpcMini/ApiChecks.lean`).
    match Eo.logos_verdict assums cmds with
    | .correct => report .correct
    | .incorrect => report .incorrect
    | .incomplete => report .incomplete (incompleteDetail assums cmds)
  | .error err =>
    IO.eprintln s!"Error parsing proof: {err}"
    return 1

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: logos-mini <path-to-proof-file>"
      return 1
  checkProof path

-- To build, run "lake build logos-mini" in this directory.
-- To run, use "lake exe logos-mini <path-to-proof-file>".
