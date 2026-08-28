module

public import Cpc.SmtEval
import all Cpc.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

mutual

/-
SMT-LIB types.
-/
inductive SmtType : Type where
  | None : SmtType
  | Bool : SmtType
  | Int : SmtType
  | Real : SmtType
  | RegLan : SmtType
  | BitVec : native_Nat -> SmtType
  | Map : SmtType -> SmtType -> SmtType
  | Set : SmtType -> SmtType
  | Seq : SmtType -> SmtType
  | Char : SmtType
  | Datatype : native_String -> SmtDatatypeDecl -> SmtType
  | TypeRef : native_String -> SmtType
  | USort : native_Nat -> SmtType
  | FunType : SmtType -> SmtType -> SmtType
  | DtcAppType : SmtType -> SmtType -> SmtType

deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : native_Bool -> SmtTerm
  | Numeral : native_Int -> SmtTerm
  | Rational : native_Rat -> SmtTerm
  | String : native_String -> SmtTerm
  | Binary : native_Int -> native_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : native_String -> SmtType -> SmtTerm
  | exists : native_String -> SmtType -> SmtTerm -> SmtTerm
  | forall : native_String -> SmtType -> SmtTerm -> SmtTerm
  | choice : native_String -> SmtType -> SmtTerm -> SmtTerm
  | bind : native_String -> SmtType -> SmtTerm -> SmtTerm -> SmtTerm
  | DtCons : native_String -> SmtDatatypeDecl -> native_Nat -> SmtTerm
  | DtSel : native_String -> SmtDatatypeDecl -> native_Nat -> native_Nat -> SmtTerm
  | DtTester : native_String -> SmtDatatypeDecl -> native_Nat -> SmtTerm
  | UConst : native_String -> SmtType -> SmtTerm
  | ite : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | not : SmtTerm -> SmtTerm
  | or : SmtTerm -> SmtTerm -> SmtTerm
  | and : SmtTerm -> SmtTerm -> SmtTerm
  | imp : SmtTerm -> SmtTerm -> SmtTerm
  | xor : SmtTerm -> SmtTerm -> SmtTerm
  | eq : SmtTerm -> SmtTerm -> SmtTerm
  | _at_purify : SmtTerm -> SmtTerm
  | plus : SmtTerm -> SmtTerm -> SmtTerm
  | neg : SmtTerm -> SmtTerm -> SmtTerm
  | mult : SmtTerm -> SmtTerm -> SmtTerm
  | lt : SmtTerm -> SmtTerm -> SmtTerm
  | leq : SmtTerm -> SmtTerm -> SmtTerm
  | gt : SmtTerm -> SmtTerm -> SmtTerm
  | geq : SmtTerm -> SmtTerm -> SmtTerm
  | to_real : SmtTerm -> SmtTerm
  | to_int : SmtTerm -> SmtTerm
  | is_int : SmtTerm -> SmtTerm
  | abs : SmtTerm -> SmtTerm
  | uneg : SmtTerm -> SmtTerm
  | div : SmtTerm -> SmtTerm -> SmtTerm
  | mod : SmtTerm -> SmtTerm -> SmtTerm
  | divisible : SmtTerm -> SmtTerm -> SmtTerm
  | int_pow2 : SmtTerm -> SmtTerm
  | int_log2 : SmtTerm -> SmtTerm
  | div_total : SmtTerm -> SmtTerm -> SmtTerm
  | mod_total : SmtTerm -> SmtTerm -> SmtTerm
  | select : SmtTerm -> SmtTerm -> SmtTerm
  | store : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | map_diff : SmtTerm -> SmtTerm -> SmtTerm
  | concat : SmtTerm -> SmtTerm -> SmtTerm
  | extract : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | repeat : SmtTerm -> SmtTerm -> SmtTerm
  | bvnot : SmtTerm -> SmtTerm
  | bvand : SmtTerm -> SmtTerm -> SmtTerm
  | bvor : SmtTerm -> SmtTerm -> SmtTerm
  | bvnand : SmtTerm -> SmtTerm -> SmtTerm
  | bvnor : SmtTerm -> SmtTerm -> SmtTerm
  | bvxor : SmtTerm -> SmtTerm -> SmtTerm
  | bvxnor : SmtTerm -> SmtTerm -> SmtTerm
  | bvcomp : SmtTerm -> SmtTerm -> SmtTerm
  | bvneg : SmtTerm -> SmtTerm
  | bvadd : SmtTerm -> SmtTerm -> SmtTerm
  | bvmul : SmtTerm -> SmtTerm -> SmtTerm
  | bvudiv : SmtTerm -> SmtTerm -> SmtTerm
  | bvurem : SmtTerm -> SmtTerm -> SmtTerm
  | bvsub : SmtTerm -> SmtTerm -> SmtTerm
  | bvsdiv : SmtTerm -> SmtTerm -> SmtTerm
  | bvsrem : SmtTerm -> SmtTerm -> SmtTerm
  | bvsmod : SmtTerm -> SmtTerm -> SmtTerm
  | bvult : SmtTerm -> SmtTerm -> SmtTerm
  | bvule : SmtTerm -> SmtTerm -> SmtTerm
  | bvugt : SmtTerm -> SmtTerm -> SmtTerm
  | bvuge : SmtTerm -> SmtTerm -> SmtTerm
  | bvslt : SmtTerm -> SmtTerm -> SmtTerm
  | bvsle : SmtTerm -> SmtTerm -> SmtTerm
  | bvsgt : SmtTerm -> SmtTerm -> SmtTerm
  | bvsge : SmtTerm -> SmtTerm -> SmtTerm
  | bvshl : SmtTerm -> SmtTerm -> SmtTerm
  | bvlshr : SmtTerm -> SmtTerm -> SmtTerm
  | bvashr : SmtTerm -> SmtTerm -> SmtTerm
  | zero_extend : SmtTerm -> SmtTerm -> SmtTerm
  | sign_extend : SmtTerm -> SmtTerm -> SmtTerm
  | rotate_left : SmtTerm -> SmtTerm -> SmtTerm
  | rotate_right : SmtTerm -> SmtTerm -> SmtTerm
  | bvuaddo : SmtTerm -> SmtTerm -> SmtTerm
  | bvnego : SmtTerm -> SmtTerm
  | bvsaddo : SmtTerm -> SmtTerm -> SmtTerm
  | bvumulo : SmtTerm -> SmtTerm -> SmtTerm
  | bvsmulo : SmtTerm -> SmtTerm -> SmtTerm
  | bvusubo : SmtTerm -> SmtTerm -> SmtTerm
  | bvssubo : SmtTerm -> SmtTerm -> SmtTerm
  | bvsdivo : SmtTerm -> SmtTerm -> SmtTerm
  | seq_empty : SmtType -> SmtTerm
  | str_len : SmtTerm -> SmtTerm
  | str_concat : SmtTerm -> SmtTerm -> SmtTerm
  | str_substr : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_contains : SmtTerm -> SmtTerm -> SmtTerm
  | str_replace : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_indexof : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_at : SmtTerm -> SmtTerm -> SmtTerm
  | str_prefixof : SmtTerm -> SmtTerm -> SmtTerm
  | str_suffixof : SmtTerm -> SmtTerm -> SmtTerm
  | str_rev : SmtTerm -> SmtTerm
  | str_update : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_to_lower : SmtTerm -> SmtTerm
  | str_to_upper : SmtTerm -> SmtTerm
  | str_to_code : SmtTerm -> SmtTerm
  | str_from_code : SmtTerm -> SmtTerm
  | str_is_digit : SmtTerm -> SmtTerm
  | str_to_int : SmtTerm -> SmtTerm
  | str_from_int : SmtTerm -> SmtTerm
  | str_lt : SmtTerm -> SmtTerm -> SmtTerm
  | str_leq : SmtTerm -> SmtTerm -> SmtTerm
  | str_replace_all : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_replace_re : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_replace_re_all : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_indexof_re : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | re_allchar : SmtTerm
  | re_none : SmtTerm
  | re_all : SmtTerm
  | str_to_re : SmtTerm -> SmtTerm
  | re_mult : SmtTerm -> SmtTerm
  | re_plus : SmtTerm -> SmtTerm
  | re_exp : SmtTerm -> SmtTerm -> SmtTerm
  | re_opt : SmtTerm -> SmtTerm
  | re_comp : SmtTerm -> SmtTerm
  | re_range : SmtTerm -> SmtTerm -> SmtTerm
  | re_concat : SmtTerm -> SmtTerm -> SmtTerm
  | re_inter : SmtTerm -> SmtTerm -> SmtTerm
  | re_union : SmtTerm -> SmtTerm -> SmtTerm
  | re_diff : SmtTerm -> SmtTerm -> SmtTerm
  | re_loop : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | str_in_re : SmtTerm -> SmtTerm -> SmtTerm
  | seq_unit : SmtTerm -> SmtTerm
  | seq_nth : SmtTerm -> SmtTerm -> SmtTerm
  | str_indexof_re_split : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | seq_diff : SmtTerm -> SmtTerm -> SmtTerm
  | _at_strings_occur_index : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | _at_strings_occur_index_re : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | set_empty : SmtType -> SmtTerm
  | set_singleton : SmtTerm -> SmtTerm
  | set_union : SmtTerm -> SmtTerm -> SmtTerm
  | set_inter : SmtTerm -> SmtTerm -> SmtTerm
  | set_minus : SmtTerm -> SmtTerm -> SmtTerm
  | set_member : SmtTerm -> SmtTerm -> SmtTerm
  | set_subset : SmtTerm -> SmtTerm -> SmtTerm
  | qdiv : SmtTerm -> SmtTerm -> SmtTerm
  | qdiv_total : SmtTerm -> SmtTerm -> SmtTerm
  | int_to_bv : SmtTerm -> SmtTerm -> SmtTerm
  | ubv_to_int : SmtTerm -> SmtTerm
  | sbv_to_int : SmtTerm -> SmtTerm

deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB values.
-/
inductive SmtValue : Type where
  | NotValue : SmtValue
  | Boolean : native_Bool -> SmtValue
  | Numeral : native_Int -> SmtValue
  | Rational : native_Rat -> SmtValue
  | Binary : native_Int -> native_Int -> SmtValue
  | Map : SmtMap -> SmtValue
  | Fun : native_String -> SmtType -> SmtType -> SmtValue
  | Set : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | Char : native_Char -> SmtValue
  | UValue : native_Nat -> native_Nat -> SmtValue
  | RegLan : SmtRegLan -> SmtValue
  | DtCons : native_String -> SmtDatatypeDecl -> native_Nat -> SmtValue
  | Apply : SmtValue -> SmtValue -> SmtValue

deriving Repr, DecidableEq, Inhabited, Ord

-- Equality of a type and of a value, which the two above are what decide.

/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)

/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

/-
Regular languages. Base elements are SmtValue, which allows regular
expression operations to be defined uniformly over the same (unpacked)
sequence representation used by the sequence operations. Well-formed
regular languages carry only valid character values as base elements, which
is what $smtx_re_canonical in tools/eoc/semantics/smt.eos decides.
-/
inductive SmtRegLan : Type where
  | empty : SmtRegLan
  | epsilon : SmtRegLan
  | char : SmtValue -> SmtRegLan
  | range : SmtValue -> SmtValue -> SmtRegLan
  | allchar : SmtRegLan
  | concat : SmtRegLan -> SmtRegLan -> SmtRegLan
  | union : SmtRegLan -> SmtRegLan -> SmtRegLan
  | inter : SmtRegLan -> SmtRegLan -> SmtRegLan
  | star : SmtRegLan -> SmtRegLan
  | comp : SmtRegLan -> SmtRegLan
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatype declarations.
-/
inductive SmtDatatypeDecl : Type where
  | nil : SmtDatatypeDecl
  | cons : native_String -> SmtDatatype -> SmtDatatypeDecl -> SmtDatatypeDecl
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving Repr, DecidableEq, Inhabited, Ord

end

end Smtm
