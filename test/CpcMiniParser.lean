import CpcMini.Parser

namespace CpcMini.Parser.Tests

open Eo

/-- The assumptions of a parsed CPCMini proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List Term) :=
  match Eo.parseProof input with
  | .ok (assums, _) => some assums
  | .error _ => none

-- The nullary `String` definition is part of the parser's initial state even
-- though its defining command does not occur in the proof.
#guard assumptions "(assume @p0 String)" ==
  some [.Apply (.UOp UserOp.Seq) (.UOp UserOp.Char)]

end CpcMini.Parser.Tests
