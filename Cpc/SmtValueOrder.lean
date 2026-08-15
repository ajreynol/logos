module

public import Cpc.SmtModelDefs
import all Cpc.SmtModelDefs

public section

set_option linter.unusedVariables false

namespace Smtm

open SmtEval

namespace SmtValueOrder

inductive Key where
  | atom : Nat → Key
  | pair : Key → Key → Key
deriving DecidableEq, Repr

@[expose] def Key.lt : Key → Key → Bool
  | .atom m, .atom n => decide (m < n)
  | .atom _, .pair _ _ => true
  | .pair _ _, .atom _ => false
  | .pair a b, .pair c d => if a = c then Key.lt b d else Key.lt a c
termination_by a b => sizeOf a + sizeOf b

@[expose] def fields : List Key → Key
  | [] => .atom 0
  | k :: ks => .pair k (fields ks)

@[expose] def node (tag : Nat) (ks : List Key) : Key :=
  .pair (.atom tag) (fields ks)

@[expose] def natKey (n : Nat) : Key := .atom n

@[expose] def boolKey : Bool → Key
  | false => .atom 0
  | true => .atom 1

@[expose] def intKey : Int → Key
  | .ofNat n => node 0 [natKey n]
  | .negSucc n => node 1 [natKey n]

@[expose] def ratKey (q : Rat) : Key :=
  node 0 [intKey q.num, natKey q.den]

@[expose] def natListKey : List Nat → Key
  | [] => .atom 0
  | n :: ns => .pair (natKey n) (natListKey ns)

mutual

@[expose] def typeKey : SmtType → Key
  | .None => node 0 []
  | .Bool => node 1 []
  | .Int => node 2 []
  | .Real => node 3 []
  | .RegLan => node 4 []
  | .BitVec w => node 5 [natKey w]
  | .Map t u => node 6 [typeKey t, typeKey u]
  | .Set t => node 7 [typeKey t]
  | .Seq t => node 8 [typeKey t]
  | .Char => node 9 []
  | .Datatype s dd => node 10 [natListKey s, datatypeDeclKey dd]
  | .TypeRef s => node 11 [natListKey s]
  | .USort n => node 12 [natKey n]
  | .FunType t u => node 13 [typeKey t, typeKey u]
  | .DtcAppType t u => node 14 [typeKey t, typeKey u]

@[expose] def valueKey : SmtValue → Key
  | .NotValue => node 0 []
  | .Boolean b => node 1 [boolKey b]
  | .Numeral i => node 2 [intKey i]
  | .Rational q => node 3 [ratKey q]
  | .Binary w i => node 4 [intKey w, intKey i]
  | .Map m => node 5 [mapKey m]
  | .Fun s t u => node 6 [natListKey s, typeKey t, typeKey u]
  | .Set m => node 7 [mapKey m]
  | .Seq s => node 8 [seqKey s]
  | .Char c => node 9 [natKey c]
  | .UValue i n => node 10 [natKey i, natKey n]
  | .RegLan r => node 11 [regLanKey r]
  | .DtCons s dd n => node 12 [natListKey s, datatypeDeclKey dd, natKey n]
  | .Apply f a => node 13 [valueKey f, valueKey a]

@[expose] def regLanKey : SmtRegLan → Key
  | .empty => node 0 []
  | .epsilon => node 1 []
  | .char c => node 2 [valueKey c]
  | .range lo hi => node 3 [valueKey lo, valueKey hi]
  | .allchar => node 4 []
  | .concat r₁ r₂ => node 5 [regLanKey r₁, regLanKey r₂]
  | .union r₁ r₂ => node 6 [regLanKey r₁, regLanKey r₂]
  | .inter r₁ r₂ => node 7 [regLanKey r₁, regLanKey r₂]
  | .star r => node 8 [regLanKey r]
  | .comp r => node 9 [regLanKey r]

@[expose] def mapKey : SmtMap → Key
  | .cons i e m => node 0 [valueKey i, valueKey e, mapKey m]
  | .default t e => node 1 [typeKey t, valueKey e]

@[expose] def seqKey : SmtSeq → Key
  | .cons v vs => node 0 [valueKey v, seqKey vs]
  | .empty t => node 1 [typeKey t]

@[expose] def datatypeDeclKey : SmtDatatypeDecl → Key
  | .nil => node 0 []
  | .cons s d dd => node 1 [natListKey s, datatypeKey d, datatypeDeclKey dd]

@[expose] def datatypeKey : SmtDatatype → Key
  | .null => node 0 []
  | .sum c d => node 1 [datatypeConsKey c, datatypeKey d]

@[expose] def datatypeConsKey : SmtDatatypeCons → Key
  | .unit => node 0 []
  | .cons t c => node 1 [typeKey t, datatypeConsKey c]

end

@[expose] def lt (a b : SmtValue) : Bool := Key.lt (valueKey a) (valueKey b)

end SmtValueOrder

end Smtm
