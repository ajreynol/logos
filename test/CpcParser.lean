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

/-!
## Syntax emitted by cvc5

Parameterized constants in CPC use flat Eunoia applications, while SMT-LIB
uses `(_ ...)`.  Numeric, symbolic, and internal-operator indices must all
produce the same terms in the two spellings.
-/

#guard assumptions "(assume @p0 (extract 1 0 #b1010))" ==
  assumptions "(assume @p0 ((_ extract 1 0) #b1010))"

#guard assumptions "(assume @p0 (@bit 0 #b1))" ==
  assumptions "(assume @p0 ((_ @bit 0) #b1))"

private def datatypePrelude : String :=
  "(declare-datatypes ((D 0)) (((a) (b)))) (declare-const d D)"

#guard assumptions (datatypePrelude ++ "(assume @p0 (is a d))") ==
  assumptions (datatypePrelude ++ "(assume @p0 ((_ is a) d))")

-- SMT-LIB type ascription supplies the same sort index as Eunoia's `_` form.
#guard assumptions "(assume @p0 (as set.empty (Set Int)))" ==
  assumptions "(assume @p0 (_ set.empty (Set Int)))"

-- Let-bound names are substituted only in the body.
#guard assumptions
    "(declare-const x Bool)
     (assume @p0 (let ((_let_1 x)) _let_1))
     (assume @p1 x)" ==
  assumptions
    "(declare-const x Bool)
     (assume @p0 x)
     (assume @p1 x)"

end Cpc.Parser.Tests
