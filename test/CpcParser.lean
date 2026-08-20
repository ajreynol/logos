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

/-!
## Overloaded names

SMT-LIB lets a symbol be declared more than once at different types, and lets a
proof's own symbol carry the name of one of the signature's operators.  A name
is then ambiguous, and the reading that has a type is the one meant.
-/

private def overloadPrelude : String :=
  "(declare-sort A 0) (declare-sort B 0)
   (declare-const f (-> A Bool)) (declare-const f (-> B Bool))
   (declare-const a A) (declare-const b B)"

-- Each use of `f` resolves to the declaration its argument fits, in either
-- order, even though the second declaration is the more recent one.
#guard assumptions (overloadPrelude ++ "(assume @p0 (f a))") ==
  some [.Apply (.UConst 1 (.Apply (.Apply .FunType (.USort 1)) .Bool)) (.UConst 3 (.USort 1))]

#guard assumptions (overloadPrelude ++ "(assume @p0 (f b))") ==
  some [.Apply (.UConst 2 (.Apply (.Apply .FunType (.USort 2)) .Bool)) (.UConst 4 (.USort 2))]

-- A symbol named after a builtin operator: `is` is also the datatype tester,
-- which does not fit an uninterpreted sort, so the declared symbol is meant.
#guard assumptions
    "(declare-sort F 0) (declare-const is (-> F Bool)) (declare-const c F)
     (assume @p0 (is c))" ==
  some [.Apply (.UConst 1 (.Apply (.Apply .FunType (.USort 1)) .Bool)) (.UConst 2 (.USort 1))]

-- The builtin still wins where it is the reading that fits.
#guard assumptions (datatypePrelude ++ "(declare-const is (-> D Bool))
     (assume @p0 (is a d))") ==
  assumptions (datatypePrelude ++ "(assume @p0 (is a d))")

end Cpc.Parser.Tests
