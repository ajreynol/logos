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

def evalLogoExpr (path : String) : Lean.Meta.MetaM Nat := do
  try
    let stx ← Lean.Parser.testParseFile (← Lean.getEnv) path
    -- IO.println stx
    let .node _ _ #[_, .node _ _ args] := stx
      | throwError "Expected a proof of the following form:\nimport Cpc.Logos\n\n#eval! <proof>\n\ngot:\n{stx}"
    Lean.liftCommandElabM do
      for arg in args do
        Lean.Elab.Command.elabCommand arg
  catch e =>
    Lean.logError m!"{e.toMessageData}"
  Lean.printTraces
  reportMessages (← Lean.Core.getMessageLog) (← Lean.getOptions) false {} 0

-- unsafe due to IO operations?
unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Cpc.Logos] {} 0 (loadExts := true)
  let path := args[0]!
  let coreContext := { fileName := path, fileMap := default }
  let coreState := { env }
  let (res, _, _) ← Lean.Meta.MetaM.toIO (evalLogoExpr path) coreContext coreState
  return res.toUInt32

-- To build, run "lake build logos" in this directory.
-- To run "lake exe logos <path-to-query-file>"
