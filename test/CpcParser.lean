import Cpc.Parser

namespace Cpc.Parser.Tests

open Eo SmtEval

/-- The assumptions of a parsed CPC proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List Term) :=
  match Eo.parseProof input with
  | .ok (assums, _) => some assums
  | .error _ => none

-- Nullary definitions from the CPC signature are available without repeating
-- their `define` commands in the proof.
#guard assumptions "(assume @p0 String)" ==
  some [.Apply (.UOp UserOp.Seq) (.UOp UserOp.Char)]

#guard assumptions "(assume @p0 @bv_empty)" == some [.Binary 0 0]

-- `_` is also Eunoia's higher-order application marker.  It remains distinct
-- from indexed syntax because `BitVec` has no one-index declaration.
#guard assumptions "(assume @p0 (_ BitVec 4))" ==
  some [.Apply (.UOp UserOp.BitVec) (.Numeral 4)]

-- Parameterized definitions are preloaded as macros and expand at their use
-- sites.  These exercise both generated CPC macros.
#guard assumptions "(assume @p0 (@bv 3 4))" ==
  some [.Apply (.UOp1 UserOp1.int_to_bv (.Numeral 4)) (.Numeral 3)]

#guard assumptions "(assume @p0 (@var \"x\" Int))" ==
  some [.Var (.String (native_string_lit "x")) (.UOp UserOp.Int)]

end Cpc.Parser.Tests
