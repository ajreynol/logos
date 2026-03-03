import Cpc.Logos
import Lean

private def reportMessages (msgLog : Lean.MessageLog) (opts : Lean.Options)
    (json : Bool) (severityOverrides : Lean.NameMap Lean.MessageSeverity) (numErrors : Nat) : IO Nat := do
  let includeEndPos := Lean.Language.printMessageEndPos.get opts
  msgLog.unreported.foldlM (init := numErrors) fun numErrors msg => do
    let numErrors := numErrors + (if msg.severity matches .error then 1 else 0)
    let maxErrorsReached := Lean.Language.maxErrors.get opts != 0 && numErrors > Lean.Language.maxErrors.get opts
    let msg : Lean.Message :=
      if maxErrorsReached then { msg with
        data := s!"maximum number of errors ({Lean.Language.maxErrors.get opts}; from option `maxErrors`) reached, exiting"
        severity := .error
      } else if let some severity := severityOverrides.find? msg.kind then
        {msg with severity}
      else
        msg
    unless msg.isSilent do
      if json then
        let j ← msg.toJson
        IO.println j.compress
      else
        let s ← msg.toString includeEndPos
        IO.print s
    if maxErrorsReached then
      IO.Process.exit 1
    return numErrors

def evalLogoExpr (path s : String) : Lean.Meta.MetaM Bool := do
  let inputCtx := Lean.Parser.InputContext.mk s path
  let pmctx  := { env := ← Lean.getEnv, options := .empty }
  let (stx, _, _) := Lean.Parser.parseCommand inputCtx pmctx {} {}
  -- IO.println stx
  Lean.liftCommandElabM (Lean.Elab.Command.elabEvalBang stx)
  Lean.printTraces
  _ ← reportMessages (← Lean.Core.getMessageLog) (← Lean.getOptions) false {} 0
  return true

-- unsafe due to IO operations?
unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Cpc.Logos] {} 0 (loadExts := true)
  let path := args[0]!
  let query ← IO.FS.readFile path
  let coreContext := { fileName := path, fileMap := default }
  let coreState := { env }
  let (res, _, _) ← Lean.Meta.MetaM.toIO (evalLogoExpr path query) coreContext coreState
  IO.println res
  return ()

-- To build, run "lake build logos" in this directory.
-- To run "lake exe logos <path-to-query-file>"
