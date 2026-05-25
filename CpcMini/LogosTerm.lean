import CpcMini.SmtEval

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo

open SmtEval

/-
Ordinary user operators.
-/
inductive UserOp : Type where
  | Int : UserOp
  | Real : UserOp
  | BitVec : UserOp
  | Char : UserOp
  | Seq : UserOp
  | not : UserOp
  | or : UserOp
  | and : UserOp
  | imp : UserOp
  | eq : UserOp

deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with one index.
-/
inductive UserOp1 : Type where
  | None : UserOp1

deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with two indices.
-/
inductive UserOp2 : Type where
  | None : UserOp2

deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with three indices.
-/
inductive UserOp3 : Type where
  | None : UserOp3

deriving Repr, DecidableEq, Inhabited, Ord

mutual

/- Term definition -/
inductive Term : Type where
  | UOp : UserOp -> Term
  | UOp1 : UserOp1 -> Term -> Term
  | UOp2 : UserOp2 -> Term -> Term -> Term
  | UOp3 : UserOp3 -> Term -> Term -> Term -> Term
  | __eo_List : Term
  | __eo_List_nil : Term
  | __eo_List_cons : Term
  | Bool : Term
  | Boolean : native_Bool -> Term
  | Numeral : native_Int -> Term
  | Rational : native_Rat -> Term
  | String : native_String -> Term
  | Binary : native_Int -> native_Int -> Term
  | Type : Term
  | Stuck : Term
  | Apply : Term -> Term -> Term
  | FunType : Term
  | Var : Term -> Term -> Term
  | DatatypeType : native_String -> Datatype -> Term
  | DatatypeTypeRef : native_String -> Term
  | DtcAppType : Term -> Term -> Term
  | DtCons : native_String -> Datatype -> native_Nat -> Term
  | DtSel : native_String -> Datatype -> native_Nat -> native_Nat -> Term
  | USort : native_Nat -> Term
  | UConst : native_Nat -> Term -> Term

deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatypes.
-/
inductive Datatype : Type where
  | null : Datatype
  | sum : DatatypeCons -> Datatype -> Datatype
deriving Repr, DecidableEq, Inhabited

/-
Eunoia datatype constructors.
-/
inductive DatatypeCons : Type where
  | unit : DatatypeCons
  | cons : Term -> DatatypeCons -> DatatypeCons
deriving Repr, DecidableEq, Inhabited

end

end Eo
