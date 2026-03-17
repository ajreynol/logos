import Cpc.Parser

def main (args : List String) : IO UInt32 := do
  let path := args[0]!
  let proof ← IO.FS.readFile path
  match Eo.parseProof proof with
  | .ok (assums, cmds) =>
    -- TODO: turn the following 4 lines into a logos API function.
    let state := Eo.logos_init_state
    let state := assums.foldl Eo.logos_invoke_assume state
    let state := Eo.__eo_invoke_cmd_list state cmds
    let result := Eo.logos_state_is_refutation state
    IO.println result
    return (!result).toUInt32
  | .error err =>
    IO.println s!"Error parsing proof: {err}"
    return 1

-- To build, run "lake build logos2" in this directory.
-- To run "lake exe logos2 <path-to-query-file>"
