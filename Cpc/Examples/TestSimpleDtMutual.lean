import Cpc.Spec

open Eo
open SmtEval
open Smtm

namespace Cpc.Examples.TestSimpleDtMutual

/-
Mutually recursive datatypes.

  (declare-datatypes ((Tree 0) (TreeList 0))
    (((node (children TreeList)))
     ((nil) (cons (head Tree) (tail TreeList)))))

`Tree` is inhabited (`node(nil)`), and both types are well formed. The terms
below mirror the encoding cvc5/Ethos emits for a self-recursive datatype (see
`examples/test-simple-dt.cpc.lean`): the body of a datatype refers to a sibling
of the mutual block with `Term.DatatypeTypeRef <name>`, and the whole block is
re-inlined at every use site as a `Term.DatatypeType <name> <body>`.

This file documents a translation bug: a `Term.DatatypeTypeRef` that points at a
*sibling* of a mutual block (rather than the enclosing self-reference) is not
handled by the SMT-side datatype machinery, so a perfectly inhabited /
well-formed mutual datatype is rejected. See the `#eval!`s at the bottom and the
explanatory comments for the expected-vs-actual results.
-/

def treeName : native_String := native_string_lit "Tree"
def listName : native_String := native_string_lit "TreeList"

/-- `TreeList` body: `nil | cons(Tree, TreeList)`. -/
def listBody : Datatype :=
  Datatype.sum DatatypeCons.unit
    (Datatype.sum
      (DatatypeCons.cons (Term.DatatypeTypeRef treeName)
        (DatatypeCons.cons (Term.DatatypeTypeRef listName) DatatypeCons.unit))
      Datatype.null)

/-- `Tree` body: `node(TreeList)`. -/
def treeBody : Datatype :=
  Datatype.sum
    (DatatypeCons.cons (Term.DatatypeTypeRef listName) DatatypeCons.unit)
    Datatype.null

def treeTypeTerm : Term := Term.DatatypeType treeName treeBody
def listTypeTerm : Term := Term.DatatypeType listName listBody

/-- The SMT types these translate to. -/
def treeSmt : SmtType := __eo_to_smt_type treeTypeTerm
def listSmt : SmtType := __eo_to_smt_type listTypeTerm

/-
A *self*-recursive control: `NatList := nil | cons(Int, NatList)`. Here the only
`DatatypeTypeRef` is the enclosing self-reference, which IS handled correctly.
-/
def natListName : native_String := native_string_lit "NatList"
def natListBody : Datatype :=
  Datatype.sum DatatypeCons.unit
    (Datatype.sum
      (DatatypeCons.cons (Term.UOp UserOp.Int)
        (DatatypeCons.cons (Term.DatatypeTypeRef natListName) DatatypeCons.unit))
      Datatype.null)
def natListTypeTerm : Term := Term.DatatypeType natListName natListBody
def natListSmt : SmtType := __eo_to_smt_type natListTypeTerm

-- Control: self-recursive datatype. All three are correct.
#eval! __smtx_type_default natListSmt    -- a real value: `nil`
#eval! native_inhabited_type natListSmt  -- true  (correct)
#eval! __smtx_type_wf natListSmt         -- true  (correct)

-- BUG 1 (well-formedness). `TreeList` is well formed, but `cons` carries a
-- `TypeRef "Tree"` that is a *sibling*, not the enclosing name "TreeList". Only
-- the enclosing name is inserted into the RefList by `__smtx_type_wf_rec`, so the
-- sibling reference fails `native_reflist_contains` and well-formedness is wrongly
-- rejected.
#eval! native_inhabited_type listSmt     -- true  (correct: nil base case)
#eval! __smtx_type_wf listSmt            -- EXPECTED true, ACTUAL false  <-- BUG

-- BUG 2 (default value / inhabitance). `Tree` is inhabited by `node(nil)`, but
-- building the default for `node` needs the default of its argument
-- `TypeRef "TreeList"`. `__smtx_type_default` has no binding for a sibling name,
-- so it returns `NotValue`; `__smtx_value_dt_substitute` only knows the single
-- enclosing binding ("Tree") and cannot fix it up. The type is therefore wrongly
-- judged uninhabited.
#eval! __smtx_type_default treeSmt       -- EXPECTED `node(nil)`, ACTUAL NotValue  <-- BUG
#eval! native_inhabited_type treeSmt     -- EXPECTED true, ACTUAL false  <-- BUG
#eval! __smtx_type_wf treeSmt            -- EXPECTED true, ACTUAL false  <-- BUG

end Cpc.Examples.TestSimpleDtMutual
