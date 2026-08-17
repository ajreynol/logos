import CpcMini.Parser

def checkProof (path : String) : IO UInt32 := do
  let proof ← IO.FS.readFile path
  match Eo.parseProof proof with
  | .ok (assums, cmds) =>
    let state := Eo.logos_init_state
    let state := assums.foldl Eo.logos_invoke_assume state
    let state := Eo.__eo_invoke_cmd_list state cmds
    let result := Eo.logos_state_is_refutation state
    if result then
      IO.println "correct"
      return 0
    else
      IO.println "incorrect"
      return 1
  | .error err =>
    IO.eprintln s!"Error parsing proof: {err}"
    return 1

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: logos-mini <path-to-proof-file>"
      return 1
  checkProof path

-- To build, run "lake build logos-mini" in this directory.
-- To run "lake exe logos-mini <path-to-query-file>"
