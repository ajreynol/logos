import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String
abbrev smt_lit_Char := Char

inductive SmtRegLan : Type where
  | empty : SmtRegLan
  | epsilon : SmtRegLan
  | char : Char -> SmtRegLan
  | range : Char -> Char -> SmtRegLan
  | allchar : SmtRegLan
  | concat : SmtRegLan -> SmtRegLan -> SmtRegLan
  | union : SmtRegLan -> SmtRegLan -> SmtRegLan
  | inter : SmtRegLan -> SmtRegLan -> SmtRegLan
  | star : SmtRegLan -> SmtRegLan
  | comp : SmtRegLan -> SmtRegLan
deriving Repr, DecidableEq, Inhabited
abbrev smt_lit_RegLan := SmtRegLan

def smt_lit_ite {T : Type} (c : smt_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev smt_lit_not := SmtEval.smt_lit_not
abbrev smt_lit_and := SmtEval.smt_lit_and
abbrev smt_lit_iff := SmtEval.smt_lit_iff
abbrev smt_lit_or := SmtEval.smt_lit_or
abbrev smt_lit_xor := SmtEval.smt_lit_xor
abbrev smt_lit_zplus := SmtEval.smt_lit_zplus
abbrev smt_lit_zmult := SmtEval.smt_lit_zmult
abbrev smt_lit_zneg := SmtEval.smt_lit_zneg
abbrev smt_lit_zeq := SmtEval.smt_lit_zeq
abbrev smt_lit_zleq := SmtEval.smt_lit_zleq
abbrev smt_lit_zlt := SmtEval.smt_lit_zlt
abbrev smt_lit_div_total := SmtEval.smt_lit_div_total
abbrev smt_lit_mod_total := SmtEval.smt_lit_mod_total
abbrev smt_lit_zexp_total := SmtEval.smt_lit_zexp_total
abbrev smt_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev smt_lit_piand := SmtEval.smt_lit_piand
abbrev smt_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev smt_lit_qplus := SmtEval.smt_lit_qplus
abbrev smt_lit_qmult := SmtEval.smt_lit_qmult
abbrev smt_lit_qneg := SmtEval.smt_lit_qneg
abbrev smt_lit_qeq := SmtEval.smt_lit_qeq
abbrev smt_lit_qleq := SmtEval.smt_lit_qleq
abbrev smt_lit_qlt := SmtEval.smt_lit_qlt
abbrev smt_lit_qdiv_total := SmtEval.smt_lit_qdiv_total
abbrev smt_lit_to_int := SmtEval.smt_lit_to_int
abbrev smt_lit_to_real := SmtEval.smt_lit_to_real
abbrev smt_lit_str_len := SmtEval.smt_lit_str_len
abbrev smt_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev smt_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev smt_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev smt_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev smt_lit_str_from_code := SmtEval.smt_lit_str_from_code
abbrev smt_lit_streq := SmtEval.smt_lit_streq

abbrev smt_lit_bit := SmtEval.smt_lit_bit
abbrev smt_lit_msb := SmtEval.smt_lit_msb
abbrev smt_lit_binary_and := SmtEval.smt_lit_binary_and
abbrev smt_lit_binary_or := SmtEval.smt_lit_binary_or
abbrev smt_lit_binary_xor := SmtEval.smt_lit_binary_xor
abbrev smt_lit_binary_not := SmtEval.smt_lit_binary_not
abbrev smt_lit_binary_max := SmtEval.smt_lit_binary_max
abbrev smt_lit_binary_uts := SmtEval.smt_lit_binary_uts
abbrev smt_lit_binary_concat := SmtEval.smt_lit_binary_concat
abbrev smt_lit_binary_extract := SmtEval.smt_lit_binary_extract

abbrev smt_lit_Nat := SmtEval.smt_lit_Nat
abbrev smt_lit_int_to_nat := SmtEval.smt_lit_int_to_nat
abbrev smt_lit_nat_to_int := SmtEval.smt_lit_nat_to_int
abbrev smt_lit_nateq := SmtEval.smt_lit_nateq
  
-- SMT Beyond Eunoia

def smt_lit_int_log2 : smt_lit_Int -> smt_lit_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))
  
def smt_lit_str_lt : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | s₁, s₂ => decide (s₁ < s₂)
def smt_lit_str_from_int : smt_lit_Int -> smt_lit_String
  | i => if i < 0 then "" else (toString i)
def smt_lit_str_to_int : smt_lit_String -> smt_lit_Int
  | s => match s.toList with
          | [] => -1
          | '0' :: _ :: _ => -1
          | cs => s.toInt?.getD (-1)
def smt_lit_str_to_upper : smt_lit_String -> smt_lit_String
  | s => s.toUpper
def smt_lit_str_to_lower : smt_lit_String -> smt_lit_String
  | s => s.toLower

-- Regular expressions

def smt_lit_re_nullable : smt_lit_RegLan -> smt_lit_Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => smt_lit_re_nullable r₁ && smt_lit_re_nullable r₂
  | .union r₁ r₂ => smt_lit_re_nullable r₁ || smt_lit_re_nullable r₂
  | .inter r₁ r₂ => smt_lit_re_nullable r₁ && smt_lit_re_nullable r₂
  | .star _ => true
  | .comp r => !(smt_lit_re_nullable r)

def smt_lit_re_mk_concat (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def smt_lit_re_mk_union (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def smt_lit_re_mk_inter (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def smt_lit_re_mk_comp : smt_lit_RegLan -> smt_lit_RegLan
  | .comp r => r
  | r => .comp r

def smt_lit_re_mk_star : smt_lit_RegLan -> smt_lit_RegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

def smt_lit_re_deriv (c : Char) : smt_lit_RegLan -> smt_lit_RegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if lo.toNat <= c.toNat && c.toNat <= hi.toNat then .epsilon else .empty
  | .allchar => .epsilon
  | .concat r₁ r₂ =>
      smt_lit_re_mk_union
        (smt_lit_re_mk_concat (smt_lit_re_deriv c r₁) r₂)
        (if smt_lit_re_nullable r₁ then smt_lit_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => smt_lit_re_mk_union (smt_lit_re_deriv c r₁) (smt_lit_re_deriv c r₂)
  | .inter r₁ r₂ => smt_lit_re_mk_inter (smt_lit_re_deriv c r₁) (smt_lit_re_deriv c r₂)
  | .star r => smt_lit_re_mk_concat (smt_lit_re_deriv c r) (.star r)
  | .comp r => smt_lit_re_mk_comp (smt_lit_re_deriv c r)

def smt_lit_re_of_list : List Char -> smt_lit_RegLan
  | [] => .epsilon
  | c :: cs => smt_lit_re_mk_concat (.char c) (smt_lit_re_of_list cs)

def smt_lit_re_prefix_match_len? (r : smt_lit_RegLan) (xs : List Char) : Option Nat :=
  let rec go (cur : smt_lit_RegLan) (rest : List Char) (n : Nat) : Option Nat :=
    if smt_lit_re_nullable cur then
      some n
    else
      match rest with
      | [] => none
      | c :: cs => go (smt_lit_re_deriv c cur) cs (n + 1)
  go r xs 0

def smt_lit_re_find_idx_aux (r : smt_lit_RegLan) (xs : List Char) (idx : Nat) : Option (Nat × Nat) :=
  match smt_lit_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => smt_lit_re_find_idx_aux r cs (idx + 1)

def smt_lit_re_find_idx_from (r : smt_lit_RegLan) (xs : List Char) (start : Nat) : Option (Nat × Nat) :=
  smt_lit_re_find_idx_aux r (xs.drop start) start

def smt_lit_re_replace_all_list_aux (fuel : Nat) (r : smt_lit_RegLan) (replacement : List Char) :
    List Char -> List Char
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match smt_lit_re_prefix_match_len? r xs with
          | some 0 =>
              match xs with
              | [] => replacement
              | c :: cs => replacement ++ (c :: smt_lit_re_replace_all_list_aux fuel r replacement cs)
          | some (n + 1) =>
              replacement ++ smt_lit_re_replace_all_list_aux fuel r replacement (xs.drop (n + 1))
          | none =>
              match xs with
              | [] => []
              | c :: cs => c :: smt_lit_re_replace_all_list_aux fuel r replacement cs

def smt_lit_re_replace_all_list (r : smt_lit_RegLan) (replacement xs : List Char) : List Char :=
  smt_lit_re_replace_all_list_aux (xs.length + 1) r replacement xs

def smt_lit_str_to_re : smt_lit_String -> smt_lit_RegLan
  | s => smt_lit_re_of_list s.toList
def smt_lit_re_mult : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_star r
def smt_lit_re_plus : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_concat r (smt_lit_re_mk_star r)
def smt_lit_re_comp : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_comp r
def smt_lit_re_concat : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_concat r₁ r₂
def smt_lit_re_inter : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_inter r₁ r₂
def smt_lit_re_diff : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_inter r₁ (smt_lit_re_mk_comp r₂)
def smt_lit_re_union : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_union r₁ r₂
def smt_lit_re_range : smt_lit_String -> smt_lit_String -> smt_lit_RegLan
  | s₁, s₂ =>
      match s₁.toList, s₂.toList with
      | [c₁], [c₂] => .range c₁ c₂
      | _, _ => .empty
def smt_lit_str_in_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Bool
  | s, r =>
      smt_lit_re_nullable <| s.toList.foldl (fun acc c => smt_lit_re_deriv c acc) r
def smt_lit_str_indexof_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Int -> smt_lit_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        match smt_lit_re_find_idx_from r s.toList (Int.toNat i) with
        | some (idx, _) => Int.ofNat idx
        | none => -1
def smt_lit_str_replace_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | s, r, replacement =>
      match smt_lit_re_find_idx_from r s.toList 0 with
      | some (idx, len) =>
          String.ofList <| (s.toList.take idx) ++ replacement.toList ++ (s.toList.drop (idx + len))
      | none => s
def smt_lit_str_replace_re_all : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | s, r, replacement => String.ofList <| smt_lit_re_replace_all_list r replacement.toList s.toList
def smt_lit_re_allchar : smt_lit_RegLan := .allchar
def smt_lit_re_none : smt_lit_RegLan := .empty
def smt_lit_re_all : smt_lit_RegLan := .star .allchar

-- Partial semantics

def smt_lit_qdiv_by_zero_id : smt_lit_String := "@qdiv_by_zero"
def smt_lit_div_by_zero_id : smt_lit_String := "@div_by_zero"
def smt_lit_mod_by_zero_id : smt_lit_String := "@mod_by_zero"
def smt_lit_wrong_apply_sel_id : smt_lit_String := "@wrong_apply_sel"
def smt_lit_uconst_id : smt_lit_Nat -> smt_lit_String
  | i => "@u." ++ toString i

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
  | BitVec : smt_lit_Int -> SmtType
  | Map : SmtType -> SmtType -> SmtType
  | DtConsType : SmtType -> SmtType -> SmtType
  | Seq : SmtType -> SmtType
  | Char : SmtType
  | Datatype : smt_lit_String -> SmtDatatype -> SmtType
  | TypeRef : smt_lit_String -> SmtType
  | USort : smt_lit_Nat -> SmtType

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : smt_lit_Bool -> SmtTerm
  | Numeral : smt_lit_Int -> SmtTerm
  | Rational : smt_lit_Rat -> SmtTerm
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : smt_lit_String -> SmtType -> SmtTerm
  | ite : SmtTerm
  | eq : SmtTerm
  | exists : smt_lit_String -> SmtType -> SmtTerm
  | forall : smt_lit_String -> SmtType -> SmtTerm
  | lambda : smt_lit_String -> SmtType -> SmtTerm
  | choice : smt_lit_String -> SmtType -> SmtTerm
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtTerm
  | DtSel : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> smt_lit_Nat -> SmtTerm
  | DtTester : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtTerm
  | UConst : smt_lit_String -> SmtType -> SmtTerm
  | not : SmtTerm
  | or : SmtTerm
  | and : SmtTerm
  | imp : SmtTerm
  | xor : SmtTerm
  | distinct : SmtTerm
  | plus : SmtTerm
  | neg : SmtTerm
  | mult : SmtTerm
  | lt : SmtTerm
  | leq : SmtTerm
  | gt : SmtTerm
  | geq : SmtTerm
  | to_real : SmtTerm
  | to_int : SmtTerm
  | is_int : SmtTerm
  | abs : SmtTerm
  | div : SmtTerm
  | mod : SmtTerm
  | multmult : SmtTerm
  | divisible : SmtTerm
  | int_pow2 : SmtTerm
  | int_log2 : SmtTerm
  | div_total : SmtTerm
  | mod_total : SmtTerm
  | multmult_total : SmtTerm
  | select : SmtTerm
  | store : SmtTerm
  | concat : SmtTerm
  | extract : SmtTerm
  | repeat : SmtTerm
  | bvnot : SmtTerm
  | bvand : SmtTerm
  | bvor : SmtTerm
  | bvnand : SmtTerm
  | bvnor : SmtTerm
  | bvxor : SmtTerm
  | bvxnor : SmtTerm
  | bvcomp : SmtTerm
  | bvneg : SmtTerm
  | bvadd : SmtTerm
  | bvmul : SmtTerm
  | bvudiv : SmtTerm
  | bvurem : SmtTerm
  | bvsub : SmtTerm
  | bvsdiv : SmtTerm
  | bvsrem : SmtTerm
  | bvsmod : SmtTerm
  | bvult : SmtTerm
  | bvule : SmtTerm
  | bvugt : SmtTerm
  | bvuge : SmtTerm
  | bvslt : SmtTerm
  | bvsle : SmtTerm
  | bvsgt : SmtTerm
  | bvsge : SmtTerm
  | bvshl : SmtTerm
  | bvlshr : SmtTerm
  | bvashr : SmtTerm
  | zero_extend : SmtTerm
  | sign_extend : SmtTerm
  | rotate_left : SmtTerm
  | rotate_right : SmtTerm
  | bvuaddo : SmtTerm
  | bvnego : SmtTerm
  | bvsaddo : SmtTerm
  | bvumulo : SmtTerm
  | bvsmulo : SmtTerm
  | bvusubo : SmtTerm
  | bvssubo : SmtTerm
  | bvsdivo : SmtTerm
  | seq_empty : SmtType -> SmtTerm
  | str_len : SmtTerm
  | str_concat : SmtTerm
  | str_substr : SmtTerm
  | str_contains : SmtTerm
  | str_replace : SmtTerm
  | str_indexof : SmtTerm
  | str_at : SmtTerm
  | str_prefixof : SmtTerm
  | str_suffixof : SmtTerm
  | str_rev : SmtTerm
  | str_update : SmtTerm
  | str_to_lower : SmtTerm
  | str_to_upper : SmtTerm
  | str_to_code : SmtTerm
  | str_from_code : SmtTerm
  | str_is_digit : SmtTerm
  | str_to_int : SmtTerm
  | str_from_int : SmtTerm
  | str_lt : SmtTerm
  | str_leq : SmtTerm
  | str_replace_all : SmtTerm
  | str_replace_re : SmtTerm
  | str_replace_re_all : SmtTerm
  | str_indexof_re : SmtTerm
  | re_allchar : SmtTerm
  | re_none : SmtTerm
  | re_all : SmtTerm
  | str_to_re : SmtTerm
  | re_mult : SmtTerm
  | re_plus : SmtTerm
  | re_exp : SmtTerm
  | re_opt : SmtTerm
  | re_comp : SmtTerm
  | re_range : SmtTerm
  | re_concat : SmtTerm
  | re_inter : SmtTerm
  | re_union : SmtTerm
  | re_diff : SmtTerm
  | re_loop : SmtTerm
  | str_in_re : SmtTerm
  | seq_unit : SmtTerm
  | seq_nth : SmtTerm
  | set_empty : SmtType -> SmtTerm
  | set_singleton : SmtTerm
  | set_union : SmtTerm
  | set_inter : SmtTerm
  | set_minus : SmtTerm
  | set_member : SmtTerm
  | set_subset : SmtTerm
  | qdiv : SmtTerm
  | qdiv_total : SmtTerm
  | int_to_bv : SmtTerm
  | ubv_to_int : SmtTerm
  | sbv_to_int : SmtTerm

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
  | NotValue : SmtValue
  | Boolean : smt_lit_Bool -> SmtValue
  | Numeral : smt_lit_Int -> SmtValue
  | Rational : smt_lit_Rat -> SmtValue
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtValue
  | Map : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | Char : smt_lit_Char -> SmtValue
  | RegLan : smt_lit_RegLan -> SmtValue
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtValue
  | Apply : SmtValue -> SmtValue -> SmtValue

deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving Repr, DecidableEq, Inhabited

end


/- SMT-LIB model -/
structure SmtModelKey where
  name : smt_lit_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

abbrev SmtModel := SmtModelKey -> Option SmtValue

def SmtModel.empty : SmtModel :=
  fun _ => none

def __smtx_model_key (s : smt_lit_String) (T : SmtType) : SmtModelKey :=
  { name := s, ty := T }

def __smtx_model_lookup (M : SmtModel) (s : smt_lit_String) (T : SmtType) : SmtValue :=
  match M (__smtx_model_key s T) with
  | some v => v
  | none => SmtValue.NotValue

def __smtx_model_push (M : SmtModel) (s : smt_lit_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  fun k =>
    if k = (__smtx_model_key s T) then
      some v
    else
      M k

/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)

macro_rules
  | `(smt_lit_veq_ext $v1 $v2) => do
      let lookupId := Lean.mkIdent `__smtx_msm_lookup
      `(by
          classical
          exact
            let lhs := $v1
            let rhs := $v2
            match lhs, rhs with
            | SmtValue.Map m1, SmtValue.Map m2 =>
                if hExt :
                    ∀ v : SmtValue,
                      $lookupId m1 v = $lookupId m2 v then
                  SmtValue.Boolean true
                else
                  SmtValue.Boolean false
            | _, _ =>
                SmtValue.Boolean (smt_lit_veq lhs rhs))
  | `(smt_lit_eval_texists $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if h :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)
  | `(smt_lit_eval_tforall $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if h :
                ∀ v : SmtValue,
                  $typeofValueId v = $T ->
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)
  | `(smt_lit_eval_tchoice $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if hSat :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              Classical.choose hSat
            else if hTy : ∃ v : SmtValue, $typeofValueId v = $T then
              Classical.choose hTy
            else
              SmtValue.NotValue)
  
/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


def __vsm_apply_arg_nth : SmtValue -> smt_lit_Nat -> SmtValue
  | (SmtValue.Apply f a), smt_lit_nat_zero => a
  | (SmtValue.Apply f a), (smt_lit_nat_succ n) => (__vsm_apply_arg_nth f n)
  | a, n => SmtValue.NotValue


def __smtx_msm_get_default : SmtMap -> SmtValue
  | (SmtMap.cons j e m) => (__smtx_msm_get_default m)
  | (SmtMap.default T e) => e


def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (smt_lit_ite (smt_lit_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => 
    let _v0 := (__smtx_typeof_map_value m)
    (smt_lit_ite (smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) _v0) _v0 SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


def __smtx_index_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => T
  | T => SmtType.None


def __smtx_elem_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => U
  | T => SmtType.None


def __smtx_mss_op_internal (isInter : smt_lit_Bool) : SmtMap -> SmtMap -> SmtMap -> SmtMap
  | (SmtMap.default T efalse), m2, acc => acc
  | (SmtMap.cons e etrue m1), m2, acc => 
    let _v0 := (SmtValue.Boolean true)
    (__smtx_mss_op_internal isInter m1 m2 (smt_lit_ite (smt_lit_iff (smt_lit_veq (__smtx_msm_lookup m2 e) _v0) isInter) (SmtMap.cons e _v0 acc) acc))


def __smtx_ssm_seq_nth : SmtSeq -> smt_lit_Int -> SmtValue
  | (SmtSeq.empty T), n => SmtValue.NotValue
  | (SmtSeq.cons v vs), 0 => v
  | (SmtSeq.cons v vs), n => (__smtx_ssm_seq_nth vs (smt_lit_zplus n (smt_lit_zneg 1)))


def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => 
    let _v0 := (__smtx_typeof_seq_value vs)
    (smt_lit_ite (smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) _v0) _v0 SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


def __smtx_dtc_concat : SmtDatatypeCons -> SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons U c1), c2 => (SmtDatatypeCons.cons U (__smtx_dtc_concat c1 c2))
  | SmtDatatypeCons.unit, c2 => c2


def __smtx_dtc_num_sels : SmtDatatypeCons -> smt_lit_Nat
  | (SmtDatatypeCons.cons U c) => (smt_lit_nat_succ (__smtx_dtc_num_sels c))
  | SmtDatatypeCons.unit => smt_lit_nat_zero


def __smtx_dt_num_sels : SmtDatatype -> smt_lit_Nat -> smt_lit_Nat
  | (SmtDatatype.sum c d), smt_lit_nat_zero => (__smtx_dtc_num_sels c)
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n) => (__smtx_dt_num_sels d n)
  | SmtDatatype.null, n => smt_lit_nat_zero


def __smtx_dtc_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons (SmtType.Datatype s2 d2) c) => (SmtDatatypeCons.cons (SmtType.Datatype s2 (smt_lit_ite (smt_lit_streq s s2) d2 (__smtx_dt_substitute s d d2))) (__smtx_dtc_substitute s d c))
  | (SmtDatatypeCons.cons T c) => (SmtDatatypeCons.cons (smt_lit_ite (smt_lit_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T) (__smtx_dtc_substitute s d c))
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit


def __smtx_dt_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatype -> SmtDatatype
  | (SmtDatatype.sum c d2) => (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d2))
  | SmtDatatype.null => SmtDatatype.null


def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> smt_lit_Nat -> SmtType
  | SmtDatatype.null, smt_lit_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), smt_lit_nat_zero => (SmtType.DtConsType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) smt_lit_nat_zero))
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n) => (__smtx_typeof_dt_cons_value_rec T d n)
  | d, n => SmtType.None


def __smtx_typeof_dt_cons_rec (T : SmtType) : SmtDatatype -> smt_lit_Nat -> SmtType
  | (SmtDatatype.sum SmtDatatypeCons.unit d), smt_lit_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), smt_lit_nat_zero => (SmtType.Map U (__smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) smt_lit_nat_zero))
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n) => (__smtx_typeof_dt_cons_rec T d n)
  | d, n => SmtType.None


def __smtx_ret_typeof_sel : SmtDatatype -> smt_lit_Nat -> smt_lit_Nat -> SmtType
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), smt_lit_nat_zero, smt_lit_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), smt_lit_nat_zero, (smt_lit_nat_succ m) => (__smtx_ret_typeof_sel (SmtDatatype.sum c d) smt_lit_nat_zero m)
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n), m => (__smtx_ret_typeof_sel d n m)
  | d, n, m => SmtType.None


def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtConsType T U), V => (smt_lit_ite (smt_lit_Teq T V) U SmtType.None)
  | T, U => SmtType.None


def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.Binary w n) => (smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.Char c) => SmtType.Char
  | (SmtValue.DtCons s d i) => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), t2, t3 => t2
  | (SmtValue.Boolean false), t2, t3 => t3
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_eq (t1 : SmtValue) (t2 : SmtValue) : SmtValue :=
  (smt_lit_veq_ext t1 t2)

def __smtx_map_select : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i => (__smtx_msm_lookup m i)
  | v, i => SmtValue.NotValue


def __smtx_map_store : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i, e => (SmtValue.Map (SmtMap.cons i e m))
  | v, i, e => SmtValue.NotValue


def __smtx_set_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal true m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


def __smtx_set_minus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal false m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


def __smtx_set_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal false m1 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false)) m2))
  | v1, v2 => SmtValue.NotValue


def __smtx_seq_nth : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq s), (SmtValue.Numeral n) => (__smtx_ssm_seq_nth s n)
  | v1, v2 => SmtValue.NotValue


def __smtx_bv_sizeof_type : SmtType -> smt_lit_Int
  | (SmtType.BitVec x1) => x1
  | t1 => (smt_lit_zneg 1)


def __smtx_bv_sizeof_value : SmtValue -> smt_lit_Int
  | (SmtValue.Binary x1 x2) => x1
  | t1 => (smt_lit_zneg 1)


def __smtx_model_eval_dt_cons (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n) SmtType.None) SmtValue.NotValue (SmtValue.DtCons s d n))

def __smtx_model_eval_dt_sel (M : SmtModel) (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) (m : smt_lit_Nat) (v : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)) (__vsm_apply_arg_nth v m) (__smtx_map_select (__smtx_map_select (__smtx_map_select (__smtx_model_lookup M smt_lit_wrong_apply_sel_id (SmtType.Map SmtType.Int (SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel d n m))))) (SmtValue.Numeral (smt_lit_nat_to_int n))) (SmtValue.Numeral (smt_lit_nat_to_int m))) v))

def __smtx_model_eval_dt_tester (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) (v1 : SmtValue) : SmtValue :=
  (SmtValue.Boolean (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n)))

def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Map m), i => (__smtx_map_select (SmtValue.Map m) i)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_or x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_imp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_not x1) x2)

def __smtx_model_eval_xor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_not (__smtx_model_eval_eq x1 x2))

def __smtx_model_eval_distinct (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_not (__smtx_model_eval_eq x1 x2))

def __smtx_model_eval_plus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zplus x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qplus x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval__ : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg x2)))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qplus x3 (smt_lit_qneg x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_mult : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zmult x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qmult x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (smt_lit_zlt x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (smt_lit_qlt x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_leq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (smt_lit_zleq x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (smt_lit_qleq x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_gt (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_lt x2 x1)

def __smtx_model_eval_geq (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_leq x2 x1)

def __smtx_model_eval_to_real : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Rational (smt_lit_to_real x1))
  | (SmtValue.Rational x2) => (SmtValue.Rational x2)
  | t1 => SmtValue.NotValue


def __smtx_model_eval_to_int : SmtValue -> SmtValue
  | (SmtValue.Rational x1) => (SmtValue.Numeral (smt_lit_to_int x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_is_int (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq (__smtx_model_eval_to_real (__smtx_model_eval_to_int x1)) x1)

def __smtx_model_eval_abs (x1 : SmtValue) : SmtValue :=
  
    let _v0 := (SmtValue.Numeral 0)
    (__smtx_model_eval_ite (__smtx_model_eval_lt x1 _v0) (__smtx_model_eval__ _v0 x1) x1)

def __smtx_model_eval_divisible (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq (__smtx_model_eval_mod_total x2 x1) (SmtValue.Numeral 0))

def __smtx_model_eval_int_pow2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (smt_lit_int_pow2 x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_int_log2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (smt_lit_int_log2 x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_div_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_div_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_mod_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_mod_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_multmult_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zexp_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_select (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_map_select x1 x2)

def __smtx_model_eval_store (x1 : SmtValue) (x2 : SmtValue) (x3 : SmtValue) : SmtValue :=
  (__smtx_map_store x1 x2 x3)

def __smtx_model_eval_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (smt_lit_zplus x1 x3)
    (SmtValue.Binary _v0 (smt_lit_mod_total (smt_lit_binary_concat x1 x2 x3 x4) (smt_lit_int_pow2 _v0)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_extract : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (smt_lit_zplus (smt_lit_zplus x1 1) (smt_lit_zneg x2))
    (SmtValue.Binary _v0 (smt_lit_mod_total (smt_lit_binary_extract x3 x4 x1 x2) (smt_lit_int_pow2 _v0)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_repeat_rec : smt_lit_Nat -> SmtValue -> SmtValue
  | smt_lit_nat_zero, x1 => (SmtValue.Binary 0 0)
  | (smt_lit_nat_succ n), x1 => (__smtx_model_eval_concat x1 (__smtx_model_eval_repeat_rec n x1))


def __smtx_model_eval_repeat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (__smtx_model_eval_repeat_rec (smt_lit_int_to_nat x1) (SmtValue.Binary x2 x3))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnot : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_not x1 x2) (smt_lit_int_pow2 x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvand : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_and x1 x2 x4) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_or x1 x2 x4) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnand (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvand x1 x2))

def __smtx_model_eval_bvnor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvor x1 x2))

def __smtx_model_eval_bvxor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_xor x1 x2 x4) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvxnor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvxor x1 x2))

def __smtx_model_eval_bvcomp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_ite (__smtx_model_eval_eq x1 x2) (SmtValue.Binary 1 1) (SmtValue.Binary 1 0))

def __smtx_model_eval_bvneg : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zneg x2) (smt_lit_int_pow2 x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvadd : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zplus x2 x4) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvmul : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zmult x2 x4) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvudiv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_ite (smt_lit_zeq x4 0) (smt_lit_binary_max x1) (smt_lit_div_total x2 x4)) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvurem : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_ite (smt_lit_zeq x4 0) x2 (smt_lit_mod_total x2 x4)) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvsub (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvadd x1 (__smtx_model_eval_bvneg x2))

def __smtx_model_eval_bvsdiv (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_bvneg x2)
    let _v1 := (__smtx_model_eval_bvneg x1)
    let _v3 := (SmtValue.Binary 1 1)
    let _v4 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x1)) (SmtValue.Numeral 1))
    let _v5 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v4 _v4 x2) _v3)
    let _v6 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v4 _v4 x1) _v3)
    let _v7 := (__smtx_model_eval_not _v6)
    let _v8 := (__smtx_model_eval_not _v5)
    (__smtx_model_eval_ite (__smtx_model_eval_and _v7 _v8) (__smtx_model_eval_bvudiv x1 x2) (__smtx_model_eval_ite (__smtx_model_eval_and _v6 _v8) (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv _v1 x2)) (__smtx_model_eval_ite (__smtx_model_eval_and _v7 _v5) (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv x1 _v0)) (__smtx_model_eval_bvudiv _v1 _v0))))

def __smtx_model_eval_bvsrem (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_bvneg x2)
    let _v1 := (__smtx_model_eval_bvneg x1)
    let _v3 := (SmtValue.Binary 1 1)
    let _v4 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x1)) (SmtValue.Numeral 1))
    let _v5 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v4 _v4 x2) _v3)
    let _v6 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v4 _v4 x1) _v3)
    let _v7 := (__smtx_model_eval_not _v6)
    let _v8 := (__smtx_model_eval_not _v5)
    (__smtx_model_eval_ite (__smtx_model_eval_and _v7 _v8) (__smtx_model_eval_bvurem x1 x2) (__smtx_model_eval_ite (__smtx_model_eval_and _v6 _v8) (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem _v1 x2)) (__smtx_model_eval_ite (__smtx_model_eval_and _v7 _v5) (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem x1 _v0)) (__smtx_model_eval_bvurem _v1 _v0))))

def __smtx_model_eval_bvsmod (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v1 := (SmtValue.Binary 1 1)
    let _v2 := (__smtx_bv_sizeof_value x1)
    let _v3 := (__smtx_model_eval__ (SmtValue.Numeral _v2) (SmtValue.Numeral 1))
    let _v4 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v3 _v3 x2) _v1)
    let _v5 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v3 _v3 x1) _v1)
    let _v6 := (__smtx_model_eval_bvurem (__smtx_model_eval_ite _v5 x1 (__smtx_model_eval_bvneg x1)) (__smtx_model_eval_ite _v4 x2 (__smtx_model_eval_bvneg x2)))
    let _v7 := (__smtx_model_eval_bvneg _v6)
    let _v8 := (__smtx_model_eval_not _v5)
    let _v9 := (__smtx_model_eval_not _v4)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v6 (SmtValue.Binary _v2 0)) _v6 (__smtx_model_eval_ite (__smtx_model_eval_and _v8 _v9) _v6 (__smtx_model_eval_ite (__smtx_model_eval_and _v5 _v9) (__smtx_model_eval_bvadd _v7 x2) (__smtx_model_eval_ite (__smtx_model_eval_and _v8 _v4) (__smtx_model_eval_bvadd _v6 x2) _v7))))

def __smtx_model_eval_bvult (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvugt x2 x1)

def __smtx_model_eval_bvule (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvuge x2 x1)

def __smtx_model_eval_bvugt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_zlt x4 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvuge (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_bvugt x1 x2) (__smtx_model_eval_eq x1 x2))

def __smtx_model_eval_bvslt (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvsgt x2 x1)

def __smtx_model_eval_bvsle (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvsge x2 x1)

def __smtx_model_eval_bvsgt (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v1 := (SmtValue.Binary 1 1)
    let _v2 := (SmtValue.Numeral 1)
    let _v3 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x2)) _v2)
    let _v4 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v3 _v3 x2) _v1)
    let _v5 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x1)) _v2)
    let _v6 := (__smtx_model_eval_eq (__smtx_model_eval_extract _v5 _v5 x1) _v1)
    (__smtx_model_eval_or (__smtx_model_eval_and (__smtx_model_eval_not _v6) _v4) (__smtx_model_eval_and (__smtx_model_eval_eq _v6 _v4) (__smtx_model_eval_bvugt x1 x2)))

def __smtx_model_eval_bvsge (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_bvsgt x1 x2) (__smtx_model_eval_eq x1 x2))

def __smtx_model_eval_bvshl : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zmult x2 (smt_lit_int_pow2 x4)) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvlshr : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_div_total x2 (smt_lit_int_pow2 x4)) (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvashr (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v1 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x1)) (SmtValue.Numeral 1))
    (__smtx_model_eval_ite (__smtx_model_eval_eq (__smtx_model_eval_extract _v1 _v1 x1) (SmtValue.Binary 1 0)) (__smtx_model_eval_bvlshr x1 x2) (__smtx_model_eval_bvnot (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot x1) x2)))

def __smtx_model_eval_zero_extend : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (SmtValue.Binary (smt_lit_zplus x1 x2) x3)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_sign_extend : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => 
    let _v0 := (smt_lit_zplus x1 x2)
    (SmtValue.Binary _v0 (smt_lit_mod_total (smt_lit_binary_uts x2 x3) (smt_lit_int_pow2 _v0)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_rotate_left_rec : smt_lit_Nat -> SmtValue -> SmtValue
  | smt_lit_nat_zero, (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 x2)
  | (smt_lit_nat_succ n), (SmtValue.Binary x1 x2) => 
    let _v0 := (SmtValue.Binary x1 x2)
    let _v1 := (smt_lit_zneg 1)
    let _v2 := (smt_lit_zplus x1 _v1)
    let _v3 := (SmtValue.Numeral _v2)
    (__smtx_model_eval_rotate_left_rec n (__smtx_model_eval_concat (__smtx_model_eval_extract (SmtValue.Numeral (smt_lit_zplus _v2 _v1)) (SmtValue.Numeral 0) _v0) (__smtx_model_eval_extract _v3 _v3 _v0)))
  | n, t1 => SmtValue.NotValue


def __smtx_model_eval_rotate_left : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), x2 => (__smtx_model_eval_rotate_left_rec (smt_lit_int_to_nat x1) x2)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_rotate_right_rec : smt_lit_Nat -> SmtValue -> SmtValue
  | smt_lit_nat_zero, (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 x2)
  | (smt_lit_nat_succ n), (SmtValue.Binary x1 x2) => 
    let _v0 := (SmtValue.Binary x1 x2)
    let _v2 := (SmtValue.Numeral 0)
    (__smtx_model_eval_rotate_right_rec n (__smtx_model_eval_concat (__smtx_model_eval_extract _v2 _v2 _v0) (__smtx_model_eval_extract (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg 1))) (SmtValue.Numeral 1) _v0)))
  | n, t1 => SmtValue.NotValue


def __smtx_model_eval_rotate_right : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), x2 => (__smtx_model_eval_rotate_right_rec (smt_lit_int_to_nat x1) x2)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvuaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_zleq (smt_lit_int_pow2 x1) (smt_lit_zplus x2 x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnego : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Boolean (smt_lit_zeq x2 (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvsaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))
    let _v1 := (smt_lit_zplus (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4))
    (SmtValue.Boolean (smt_lit_or (smt_lit_zleq _v0 _v1) (smt_lit_zlt _v1 (smt_lit_zneg _v0))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvumulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_zleq (smt_lit_int_pow2 x1) (smt_lit_zmult x2 x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvsmulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))
    let _v1 := (smt_lit_zmult (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4))
    (SmtValue.Boolean (smt_lit_or (smt_lit_zleq _v0 _v1) (smt_lit_zlt _v1 (smt_lit_zneg _v0))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvusubo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvult x1 x2)

def __smtx_model_eval_bvssubo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_ite (__smtx_model_eval_bvnego x2) (__smtx_model_eval_bvsge x1 (SmtValue.Binary (__smtx_bv_sizeof_value x1) 0)) (__smtx_model_eval_bvsaddo x1 (__smtx_model_eval_bvneg x2)))

def __smtx_model_eval_bvsdivo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_and (__smtx_model_eval_bvnego x1) (__smtx_model_eval_eq x2 (__smtx_model_eval_bvnot (SmtValue.Binary (__smtx_bv_sizeof_value x1) 0))))

def __smtx_model_eval_str_len : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (smt_lit_seq_len (smt_lit_unpack_seq x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_concat (smt_lit_unpack_seq x1) (smt_lit_unpack_seq x2))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_substr : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Numeral x2), (SmtValue.Numeral x3) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_extract (smt_lit_unpack_seq x1) x2 x3)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_contains : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Boolean (smt_lit_seq_contains (smt_lit_unpack_seq x1) (smt_lit_unpack_seq x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_replace : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Seq x3) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_replace (smt_lit_unpack_seq x1) (smt_lit_unpack_seq x2) (smt_lit_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_indexof : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (smt_lit_seq_indexof (smt_lit_unpack_seq x1) (smt_lit_unpack_seq x2) x3))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_at (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_str_substr x1 x2 (SmtValue.Numeral 1))

def __smtx_model_eval_str_prefixof (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq x1 (__smtx_model_eval_str_substr x2 (SmtValue.Numeral 0) (__smtx_model_eval_str_len x1)))

def __smtx_model_eval_str_suffixof (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_str_len x1)
    (__smtx_model_eval_eq x1 (__smtx_model_eval_str_substr x2 (__smtx_model_eval__ (__smtx_model_eval_str_len x2) _v0) _v0))

def __smtx_model_eval_str_rev : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_rev (smt_lit_unpack_seq x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_update : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Numeral x2), (SmtValue.Seq x3) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_update (smt_lit_unpack_seq x1) x2 (smt_lit_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_to_lower : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_to_lower (smt_lit_unpack_string x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_to_upper : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_to_upper (smt_lit_unpack_string x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_to_code : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (smt_lit_str_to_code (smt_lit_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_from_code : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_from_code x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_is_digit (x1 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_str_to_code x1)
    (__smtx_model_eval_and (__smtx_model_eval_leq (SmtValue.Numeral 48) _v0) (__smtx_model_eval_leq _v0 (SmtValue.Numeral 57)))

def __smtx_model_eval_str_to_int : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (smt_lit_str_to_int (smt_lit_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_from_int : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_from_int x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Boolean (smt_lit_str_lt (smt_lit_unpack_string x1) (smt_lit_unpack_string x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_leq (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_eq x1 x2) (__smtx_model_eval_str_lt x1 x2))

def __smtx_model_eval_str_replace_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Seq x3) => (SmtValue.Seq (smt_lit_pack_seq (__smtx_typeof_seq_value x1) (smt_lit_seq_replace_all (smt_lit_unpack_seq x1) (smt_lit_unpack_seq x2) (smt_lit_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_replace_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Seq x3) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_replace_re (smt_lit_unpack_string x1) x2 (smt_lit_unpack_string x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_replace_re_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Seq x3) => (SmtValue.Seq (smt_lit_pack_string (smt_lit_str_replace_re_all (smt_lit_unpack_string x1) x2 (smt_lit_unpack_string x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_indexof_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (smt_lit_str_indexof_re (smt_lit_unpack_string x1) x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_to_re : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.RegLan (smt_lit_str_to_re (smt_lit_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_mult : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (smt_lit_re_mult x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_plus (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_re_concat x1 (__smtx_model_eval_re_mult x1))

def __smtx_model_eval_re_exp_rec : smt_lit_Nat -> SmtValue -> SmtValue
  | smt_lit_nat_zero, x1 => (SmtValue.RegLan (smt_lit_str_to_re (smt_lit_unpack_string (SmtSeq.empty SmtType.Char))))
  | (smt_lit_nat_succ n), x1 => (__smtx_model_eval_re_concat (__smtx_model_eval_re_exp_rec n x1) x1)


def __smtx_model_eval_re_exp : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.RegLan x2) => (__smtx_model_eval_re_exp_rec (smt_lit_int_to_nat x1) (SmtValue.RegLan x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_opt (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_re_union x1 (SmtValue.RegLan (smt_lit_str_to_re (smt_lit_unpack_string (SmtSeq.empty SmtType.Char)))))

def __smtx_model_eval_re_comp : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (smt_lit_re_comp x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_range : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.RegLan (smt_lit_re_range (smt_lit_unpack_string x1) (smt_lit_unpack_string x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_concat x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_inter x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_union x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_diff : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_diff x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_loop_rec : smt_lit_Nat -> SmtValue -> SmtValue -> SmtValue -> SmtValue
  | smt_lit_nat_zero, x1, (SmtValue.Numeral x2), x3 => (__smtx_model_eval_re_exp x1 x3)
  | (smt_lit_nat_succ n), x1, (SmtValue.Numeral x2), x3 => (__smtx_model_eval_re_union (__smtx_model_eval_re_loop_rec n x1 (SmtValue.Numeral (smt_lit_zplus x2 (smt_lit_zneg 1))) x3) (__smtx_model_eval_re_exp (SmtValue.Numeral x2) x3))
  | n, t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_re_loop : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2), (SmtValue.RegLan x3) => 
    let _v0 := (SmtValue.Numeral x2)
    let _v1 := (SmtValue.Numeral x1)
    (__smtx_model_eval_ite (__smtx_model_eval_gt _v1 _v0) (SmtValue.RegLan smt_lit_re_none) (__smtx_model_eval_re_loop_rec (smt_lit_int_to_nat (smt_lit_zplus x2 (smt_lit_zneg x1))) _v1 _v0 (SmtValue.RegLan x3)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_in_re : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2) => (SmtValue.Boolean (smt_lit_str_in_re (smt_lit_unpack_string x1) x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_set_singleton (x1 : SmtValue) : SmtValue :=
  (SmtValue.Map (SmtMap.cons x1 (SmtValue.Boolean true) (SmtMap.default (__smtx_typeof_value x1) (SmtValue.Boolean false))))

def __smtx_model_eval_set_union (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_set_union x1 x2)

def __smtx_model_eval_set_inter (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_set_inter x1 x2)

def __smtx_model_eval_set_minus (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_set_minus x1 x2)

def __smtx_model_eval_set_member (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_map_select x2 x1)

def __smtx_model_eval_set_subset (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq (__smtx_model_eval_set_inter x1 x2) x1)

def __smtx_model_eval_qdiv_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Rational (smt_lit_mk_rational x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qdiv_total x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_int_to_bv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Binary x1 (smt_lit_mod_total x2 (smt_lit_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_ubv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral x2)
  | t1 => SmtValue.NotValue


def __smtx_model_eval_sbv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral (smt_lit_binary_uts x1 x2))
  | t1 => SmtValue.NotValue


def __smtx_typeof_guard (T : SmtType) (U : SmtType) : SmtType :=
  (smt_lit_ite (smt_lit_Teq T SmtType.None) SmtType.None U)

def __smtx_typeof_ite : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Bool, U, V => (smt_lit_ite (smt_lit_Teq U V) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_eq (T : SmtType) (U : SmtType) : SmtType :=
  (__smtx_typeof_guard T (smt_lit_ite (smt_lit_Teq T U) SmtType.Bool SmtType.None))

def __smtx_typeof_apply : SmtType -> SmtType -> SmtType
  | (SmtType.Map T U), V => (__smtx_typeof_guard T (smt_lit_ite (smt_lit_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_bv_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n1), (SmtType.BitVec n2) => (smt_lit_ite (smt_lit_zeq n1 n2) (SmtType.BitVec n1) SmtType.None)
  | T, U => SmtType.None


def __smtx_typeof_bv_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n1), (SmtType.BitVec n2), U => (smt_lit_ite (smt_lit_zeq n1 n2) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_sets_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 SmtType.Bool), (SmtType.Map x2 SmtType.Bool) => (smt_lit_ite (smt_lit_Teq x1 x2) (SmtType.Map x1 SmtType.Bool) SmtType.None)
  | x1, x2 => SmtType.None


def __smtx_typeof_sets_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 SmtType.Bool), (SmtType.Map x2 SmtType.Bool), T => (smt_lit_ite (smt_lit_Teq x1 x2) T SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_seq_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2) => (smt_lit_ite (smt_lit_Teq x1 x2) (SmtType.Seq x1) SmtType.None)
  | x1, x2 => SmtType.None


def __smtx_typeof_seq_op_3 : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2), (SmtType.Seq x3) => (smt_lit_ite (smt_lit_Teq x1 x2) (smt_lit_ite (smt_lit_Teq x2 x3) (SmtType.Seq x1) SmtType.None) SmtType.None)
  | x1, x2, x3 => SmtType.None


def __smtx_typeof_seq_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2), T => (smt_lit_ite (smt_lit_Teq x1 x2) T SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_bv_op_1 : SmtType -> SmtType
  | (SmtType.BitVec n) => (SmtType.BitVec n)
  | T => SmtType.None


def __smtx_typeof_bv_op_1_ret : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n), T => T
  | T, U => SmtType.None


def __smtx_typeof_arith_overload_op_2 : SmtType -> SmtType -> SmtType
  | SmtType.Int, SmtType.Int => SmtType.Int
  | SmtType.Real, SmtType.Real => SmtType.Real
  | T, U => SmtType.None


def __smtx_typeof_arith_overload_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Int, SmtType.Int, T => T
  | SmtType.Real, SmtType.Real, T => T
  | T, U, V => SmtType.None


def __smtx_typeof_select : SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 x2), x3 => (smt_lit_ite (smt_lit_Teq x1 x3) x2 SmtType.None)
  | x4, x5 => SmtType.None


def __smtx_typeof_store : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 x2), x3, x4 => (smt_lit_ite (smt_lit_Teq x1 x3) (smt_lit_ite (smt_lit_Teq x2 x4) (SmtType.Map x1 x2) SmtType.None) SmtType.None)
  | x5, x6, x7 => SmtType.None


def __smtx_typeof_concat : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec x1), (SmtType.BitVec x2) => (SmtType.BitVec (smt_lit_zplus x1 x2))
  | x3, x4 => SmtType.None


def __smtx_typeof_extract : SmtTerm -> SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtTerm.Numeral x2), (SmtType.BitVec x3) => (smt_lit_ite (smt_lit_zleq 0 x2) (smt_lit_ite (smt_lit_zleq x2 x1) (smt_lit_ite (smt_lit_zlt x1 x3) (SmtType.BitVec (smt_lit_zplus (smt_lit_zplus x2 (smt_lit_zneg x1)) 1)) SmtType.None) SmtType.None) SmtType.None)
  | x4, x5, x6 => SmtType.None


def __smtx_typeof_repeat : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (smt_lit_ite (smt_lit_zleq 1 x1) (SmtType.BitVec (smt_lit_zmult x1 x2)) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_zero_extend : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtType.BitVec (smt_lit_zplus x1 x2)) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_sign_extend : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtType.BitVec (smt_lit_zplus x1 x2)) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_rotate_left : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtType.BitVec x2) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_rotate_right : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtType.BitVec x2) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_re_exp : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), SmtType.RegLan => (smt_lit_ite (smt_lit_zleq 0 x1) SmtType.RegLan SmtType.None)
  | x2, x3 => SmtType.None


def __smtx_typeof_re_loop : SmtTerm -> SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtTerm.Numeral x2), SmtType.RegLan => (smt_lit_ite (smt_lit_zleq 0 x1) (smt_lit_ite (smt_lit_zleq 0 x2) SmtType.RegLan SmtType.None) SmtType.None)
  | x3, x4, x5 => SmtType.None


def __smtx_typeof_seq_nth : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), SmtType.Int => x1
  | x2, x3 => SmtType.None


def __smtx_typeof_set_member : SmtType -> SmtType -> SmtType
  | x1, (SmtType.Map x2 SmtType.Bool) => (smt_lit_ite (smt_lit_Teq x1 x2) SmtType.Bool SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_int_to_bv : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), SmtType.Int => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtType.BitVec x1) SmtType.None)
  | x2, x3 => SmtType.None


def __smtx_typeof : SmtTerm -> SmtType
  | (SmtTerm.Boolean b) => SmtType.Bool
  | (SmtTerm.Numeral n) => SmtType.Int
  | (SmtTerm.Rational r) => SmtType.Real
  | (SmtTerm.Binary w n) => (smt_lit_ite (smt_lit_and (smt_lit_zleq 0 w) (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))) (SmtType.BitVec w) SmtType.None)
  | (SmtTerm.Apply SmtTerm.not x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2) => (__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply SmtTerm.to_real x1) => 
    let _v0 := (__smtx_typeof x1)
    (smt_lit_ite (smt_lit_Teq _v0 SmtType.Int) SmtType.Real (smt_lit_ite (smt_lit_Teq _v0 SmtType.Real) SmtType.Real SmtType.None))
  | (SmtTerm.Apply SmtTerm.to_int x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Real) SmtType.Int SmtType.None)
  | (SmtTerm.Apply SmtTerm.is_int x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Real) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply SmtTerm.abs x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply SmtTerm.int_pow2 x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply SmtTerm.int_log2 x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select x1) x2) => (__smtx_typeof_select (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store x1) x2) x3) => (__smtx_typeof_store (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat x1) x2) => (__smtx_typeof_concat (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract x1) x2) x3) => (__smtx_typeof_extract x1 x2 (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat x1) x2) => (__smtx_typeof_repeat x1 (__smtx_typeof x2))
  | (SmtTerm.Apply SmtTerm.bvnot x1) => (__smtx_typeof_bv_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) (SmtType.BitVec 1))
  | (SmtTerm.Apply SmtTerm.bvneg x1) => (__smtx_typeof_bv_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend x1) x2) => (__smtx_typeof_zero_extend x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend x1) x2) => (__smtx_typeof_sign_extend x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left x1) x2) => (__smtx_typeof_rotate_left x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right x1) x2) => (__smtx_typeof_rotate_right x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply SmtTerm.bvnego x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.seq_empty x1) => (SmtType.Seq x1)
  | (SmtTerm.Apply SmtTerm.str_len x1) => SmtType.None
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat x1) x2) => (__smtx_typeof_seq_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x1) x2) x3) => SmtType.None
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains x1) x2) => (__smtx_typeof_seq_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace x1) x2) x3) => (__smtx_typeof_seq_op_3 (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof x1) x2) x3) => SmtType.None
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at x1) x2) => SmtType.None
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_rev x1) => SmtType.None
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update x1) x2) x3) => SmtType.None
  | (SmtTerm.Apply SmtTerm.str_to_lower x1) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) _v0 SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_to_upper x1) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) _v0 SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_to_code x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Int SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_from_code x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_is_digit x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_to_int x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Int SmtType.None)
  | (SmtTerm.Apply SmtTerm.str_from_int x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Int) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all x1) x2) x3) => (__smtx_typeof_seq_op_3 (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re x1) x2) x3) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x3) _v0) _v0 SmtType.None) SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all x1) x2) x3) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x3) _v0) _v0 SmtType.None) SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re x1) x2) x3) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x3) SmtType.Int) SmtType.Int SmtType.None) SmtType.None) SmtType.None)
  | SmtTerm.re_allchar => SmtType.RegLan
  | SmtTerm.re_none => SmtType.RegLan
  | SmtTerm.re_all => SmtType.RegLan
  | (SmtTerm.Apply SmtTerm.str_to_re x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply SmtTerm.re_mult x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply SmtTerm.re_plus x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp x1) x2) => (__smtx_typeof_re_exp x1 (__smtx_typeof x2))
  | (SmtTerm.Apply SmtTerm.re_opt x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply SmtTerm.re_comp x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) _v0) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) _v0) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.RegLan) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop x1) x2) x3) => (__smtx_typeof_re_loop x1 x2 (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re x1) x2) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply SmtTerm.seq_unit x1) => 
    let _v0 := (__smtx_typeof x1)
    (smt_lit_ite (smt_lit_Teq _v0 SmtType.None) SmtType.None (SmtType.Seq _v0))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth x1) x2) => (__smtx_typeof_seq_nth (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.set_empty x1) => (SmtType.Map x1 SmtType.Bool)
  | (SmtTerm.Apply SmtTerm.set_singleton x1) => 
    let _v0 := (__smtx_typeof x1)
    (smt_lit_ite (smt_lit_Teq _v0 SmtType.None) SmtType.None (SmtType.Map _v0 SmtType.Bool))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member x1) x2) => (__smtx_typeof_set_member (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset x1) x2) => (__smtx_typeof_sets_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Real)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Real)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv x1) x2) => (__smtx_typeof_int_to_bv x1 (__smtx_typeof x2))
  | (SmtTerm.Apply SmtTerm.ubv_to_int x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Int)
  | (SmtTerm.Apply SmtTerm.sbv_to_int x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Int)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite x1) x2) x3) => (__smtx_typeof_ite (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.choice s T) x1) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool) T SmtType.None)
  | (SmtTerm.DtCons s d i) => (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i)
  | (SmtTerm.DtSel s d i j) => (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel (__smtx_dt_substitute s d d) i j))
  | (SmtTerm.DtTester s d i) => (SmtType.Map (SmtType.Datatype s d) SmtType.Bool)
  | (SmtTerm.Apply f x1) => (__smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x1))
  | (SmtTerm.Var s T) => T
  | (SmtTerm.UConst s T) => T
  | x1 => SmtType.None




def smt_lit_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (smt_lit_unpack_seq vs)
  | (SmtSeq.empty _) => []


def smt_lit_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (smt_lit_pack_seq T vs))


def __smtx_ssm_char_values_of_string (s : smt_lit_String) : List SmtValue :=
  s.toList.map SmtValue.Char

def __smtx_ssm_char_of_value : SmtValue -> Char
  | (SmtValue.Char c) => c
  | _ => Char.ofNat 0

def __smtx_ssm_string_of_char_values (xs : List SmtValue) : smt_lit_String :=
  String.ofList (xs.map __smtx_ssm_char_of_value)

def smt_lit_unpack_string (x : SmtSeq) : smt_lit_String :=
  (__smtx_ssm_string_of_char_values (smt_lit_unpack_seq x))

def smt_lit_pack_string (s : smt_lit_String) : SmtSeq :=
  (smt_lit_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s))

  
def __smtx_value_eqb (v1 : SmtValue) (v2 : SmtValue) : smt_lit_Bool :=
  match __smtx_model_eval_eq v1 v2 with
  | (SmtValue.Boolean b) => b
  | _ => false


def smt_lit_seq_prefix_eq : List SmtValue -> List SmtValue -> smt_lit_Bool
  | [], _ => true
  | _ :: _, [] => false
  | v1 :: vs1, v2 :: vs2 => (__smtx_value_eqb v1 v2) && (smt_lit_seq_prefix_eq vs1 vs2)


def smt_lit_seq_len : List SmtValue -> smt_lit_Int
  | x => Int.ofNat x.length

def smt_lit_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y
  
def smt_lit_seq_extract (xs : List SmtValue) (i : smt_lit_Int) (n : smt_lit_Int) : List SmtValue :=
  let len : smt_lit_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take


def smt_lit_seq_indexof_rec (xs pat : List SmtValue) (i fuel : Nat) : smt_lit_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if smt_lit_seq_prefix_eq pat xs then
        Int.ofNat i
      else
        match xs with
        | [] => -1
        | _ :: ys => (smt_lit_seq_indexof_rec ys pat (i + 1) fuel)


def smt_lit_seq_indexof (xs pat : List SmtValue) (i : smt_lit_Int) : smt_lit_Int :=
  if i < 0 then
    -1
  else
    let start := Int.toNat i
    let patLen := pat.length
    let xsLen := xs.length
    if h : start + patLen <= xsLen then
      (smt_lit_seq_indexof_rec (xs.drop start) pat start (xsLen - (start + patLen) + 1))
    else
      -1


def smt_lit_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  match pat with
  | [] => repl ++ xs
  | _ =>
      let idx := smt_lit_seq_indexof xs pat 0
      if idx < 0 then
        xs
      else
        let n := Int.toNat idx
        (xs.take n) ++ repl ++ (xs.drop (n + pat.length))


def smt_lit_seq_replace_all_aux (fuel : Nat) (pat repl : List SmtValue) :
    List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := smt_lit_seq_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                (xs.take n) ++ repl ++
                  (smt_lit_seq_replace_all_aux fuel pat repl (xs.drop (n + pat.length)))


def smt_lit_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  (smt_lit_seq_replace_all_aux (xs.length + 1) pat repl xs)


def smt_lit_seq_update (xs : List SmtValue) (i : smt_lit_Int) (ys : List SmtValue) : List SmtValue :=
  let len : smt_lit_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ ys ++ (xs.drop (idx + 1))
    
def smt_lit_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse
  
def smt_lit_seq_contains (xs pat : List SmtValue) : smt_lit_Bool :=
  (0 <= (smt_lit_seq_indexof xs pat 0))

end

end

noncomputable def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.Binary w n) => (SmtValue.Binary w n)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or x1) x2) => (__smtx_model_eval_or (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp x1) x2) => (__smtx_model_eval_imp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) => (__smtx_model_eval_xor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2) => (__smtx_model_eval_distinct (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus x1) x2) => (__smtx_model_eval_plus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg x1) x2) => (__smtx_model_eval__ (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult x1) x2) => (__smtx_model_eval_mult (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt x1) x2) => (__smtx_model_eval_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq x1) x2) => (__smtx_model_eval_leq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt x1) x2) => (__smtx_model_eval_gt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) x2) => (__smtx_model_eval_geq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.to_real x1) => (__smtx_model_eval_to_real (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.to_int x1) => (__smtx_model_eval_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.is_int x1) => (__smtx_model_eval_is_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.abs x1) => (__smtx_model_eval_abs (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0)) (__smtx_model_eval_apply (__smtx_model_lookup M smt_lit_div_by_zero_id (SmtType.Map SmtType.Int SmtType.Int)) _v1) (__smtx_model_eval_div_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0)) (__smtx_model_eval_apply (__smtx_model_lookup M smt_lit_mod_by_zero_id (SmtType.Map SmtType.Int SmtType.Int)) _v1) (__smtx_model_eval_mod_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (SmtValue.Numeral 0)
    let _v2 := (__smtx_model_eval M x1)
    let _v3 := (SmtValue.Numeral 1)
    (__smtx_model_eval_ite (__smtx_model_eval_geq _v0 _v1) (__smtx_model_eval_multmult_total _v2 _v0) (__smtx_model_eval_ite (__smtx_model_eval_eq _v2 _v1) (__smtx_model_eval_apply (__smtx_model_lookup M smt_lit_div_by_zero_id (SmtType.Map SmtType.Int SmtType.Int)) _v3) (__smtx_model_eval_div_total _v3 (__smtx_model_eval_multmult_total _v2 (__smtx_model_eval__ _v1 _v0)))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible x1) x2) => (__smtx_model_eval_divisible (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.int_pow2 x1) => (__smtx_model_eval_int_pow2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.int_log2 x1) => (__smtx_model_eval_int_log2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total x1) x2) => (__smtx_model_eval_div_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total x1) x2) => (__smtx_model_eval_mod_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total x1) x2) => (__smtx_model_eval_multmult_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select x1) x2) => (__smtx_model_eval_select (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store x1) x2) x3) => (__smtx_model_eval_store (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat x1) x2) => (__smtx_model_eval_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract x1) x2) x3) => (__smtx_model_eval_extract (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat x1) x2) => (__smtx_model_eval_repeat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.bvnot x1) => (__smtx_model_eval_bvnot (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand x1) x2) => (__smtx_model_eval_bvand (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor x1) x2) => (__smtx_model_eval_bvor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand x1) x2) => (__smtx_model_eval_bvnand (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor x1) x2) => (__smtx_model_eval_bvnor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor x1) x2) => (__smtx_model_eval_bvxor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor x1) x2) => (__smtx_model_eval_bvxnor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp x1) x2) => (__smtx_model_eval_bvcomp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.bvneg x1) => (__smtx_model_eval_bvneg (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd x1) x2) => (__smtx_model_eval_bvadd (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul x1) x2) => (__smtx_model_eval_bvmul (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv x1) x2) => (__smtx_model_eval_bvudiv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem x1) x2) => (__smtx_model_eval_bvurem (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub x1) x2) => (__smtx_model_eval_bvsub (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv x1) x2) => (__smtx_model_eval_bvsdiv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem x1) x2) => (__smtx_model_eval_bvsrem (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod x1) x2) => (__smtx_model_eval_bvsmod (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult x1) x2) => (__smtx_model_eval_bvult (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule x1) x2) => (__smtx_model_eval_bvule (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x1) x2) => (__smtx_model_eval_bvugt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge x1) x2) => (__smtx_model_eval_bvuge (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt x1) x2) => (__smtx_model_eval_bvslt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle x1) x2) => (__smtx_model_eval_bvsle (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt x1) x2) => (__smtx_model_eval_bvsgt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge x1) x2) => (__smtx_model_eval_bvsge (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl x1) x2) => (__smtx_model_eval_bvshl (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr x1) x2) => (__smtx_model_eval_bvlshr (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr x1) x2) => (__smtx_model_eval_bvashr (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend x1) x2) => (__smtx_model_eval_zero_extend (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend x1) x2) => (__smtx_model_eval_sign_extend (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left x1) x2) => (__smtx_model_eval_rotate_left (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right x1) x2) => (__smtx_model_eval_rotate_right (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo x1) x2) => (__smtx_model_eval_bvuaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.bvnego x1) => (__smtx_model_eval_bvnego (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo x1) x2) => (__smtx_model_eval_bvsaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo x1) x2) => (__smtx_model_eval_bvumulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo x1) x2) => (__smtx_model_eval_bvsmulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo x1) x2) => (__smtx_model_eval_bvusubo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo x1) x2) => (__smtx_model_eval_bvssubo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo x1) x2) => (__smtx_model_eval_bvsdivo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.seq_empty x1) => (SmtValue.Seq (SmtSeq.empty x1))
  | (SmtTerm.Apply SmtTerm.str_len x1) => (__smtx_model_eval_str_len (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat x1) x2) => (__smtx_model_eval_str_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x1) x2) x3) => (__smtx_model_eval_str_substr (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains x1) x2) => (__smtx_model_eval_str_contains (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace x1) x2) x3) => (__smtx_model_eval_str_replace (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof x1) x2) x3) => (__smtx_model_eval_str_indexof (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at x1) x2) => (__smtx_model_eval_str_at (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof x1) x2) => (__smtx_model_eval_str_prefixof (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof x1) x2) => (__smtx_model_eval_str_suffixof (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.str_rev x1) => (__smtx_model_eval_str_rev (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update x1) x2) x3) => (__smtx_model_eval_str_update (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply SmtTerm.str_to_lower x1) => (__smtx_model_eval_str_to_lower (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_to_upper x1) => (__smtx_model_eval_str_to_upper (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_to_code x1) => (__smtx_model_eval_str_to_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_from_code x1) => (__smtx_model_eval_str_from_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_is_digit x1) => (__smtx_model_eval_str_is_digit (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_to_int x1) => (__smtx_model_eval_str_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_from_int x1) => (__smtx_model_eval_str_from_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt x1) x2) => (__smtx_model_eval_str_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq x1) x2) => (__smtx_model_eval_str_leq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all x1) x2) x3) => (__smtx_model_eval_str_replace_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re x1) x2) x3) => (__smtx_model_eval_str_replace_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all x1) x2) x3) => (__smtx_model_eval_str_replace_re_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re x1) x2) x3) => (__smtx_model_eval_str_indexof_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | SmtTerm.re_allchar => (SmtValue.RegLan smt_lit_re_allchar)
  | SmtTerm.re_none => (SmtValue.RegLan smt_lit_re_none)
  | SmtTerm.re_all => (SmtValue.RegLan smt_lit_re_all)
  | (SmtTerm.Apply SmtTerm.str_to_re x1) => (__smtx_model_eval_str_to_re (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.re_mult x1) => (__smtx_model_eval_re_mult (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.re_plus x1) => (__smtx_model_eval_re_plus (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp x1) x2) => (__smtx_model_eval_re_exp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.re_opt x1) => (__smtx_model_eval_re_opt (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.re_comp x1) => (__smtx_model_eval_re_comp (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range x1) x2) => (__smtx_model_eval_re_range (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat x1) x2) => (__smtx_model_eval_re_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter x1) x2) => (__smtx_model_eval_re_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union x1) x2) => (__smtx_model_eval_re_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff x1) x2) => (__smtx_model_eval_re_diff (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop x1) x2) x3) => (__smtx_model_eval_re_loop (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re x1) x2) => (__smtx_model_eval_str_in_re (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.seq_unit x1) => 
    let _v0 := (__smtx_model_eval M x1)
    (SmtValue.Seq (SmtSeq.cons _v0 (SmtSeq.empty (__smtx_typeof_value _v0))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth x1) x2) => (__smtx_seq_nth (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.set_empty x1) => (SmtValue.Map (SmtMap.default x1 (SmtValue.Boolean false)))
  | (SmtTerm.Apply SmtTerm.set_singleton x1) => (__smtx_model_eval_set_singleton (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union x1) x2) => (__smtx_model_eval_set_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter x1) x2) => (__smtx_model_eval_set_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus x1) x2) => (__smtx_model_eval_set_minus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member x1) x2) => (__smtx_model_eval_set_member (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset x1) x2) => (__smtx_model_eval_set_subset (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Rational (smt_lit_mk_rational 0 1))) (__smtx_model_eval_apply (__smtx_model_lookup M smt_lit_qdiv_by_zero_id (SmtType.Map SmtType.Real SmtType.Real)) _v1) (__smtx_model_eval_qdiv_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total x1) x2) => (__smtx_model_eval_qdiv_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv x1) x2) => (__smtx_model_eval_int_to_bv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.ubv_to_int x1) => (__smtx_model_eval_ubv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.sbv_to_int x1) => (__smtx_model_eval_sbv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite x1) x2) x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit_eval_texists M s T x1)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit_eval_tforall M s T x1)
  | (SmtTerm.Apply (SmtTerm.choice s T) x1) => (smt_lit_eval_tchoice M s T x1)
  | (SmtTerm.DtCons s d i) => (__smtx_model_eval_dt_cons s d i)
  | (SmtTerm.Apply (SmtTerm.DtSel s d i j) x1) => (__smtx_model_eval_dt_sel M s d i j (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s d i) x1) => (__smtx_model_eval_dt_tester s d i (__smtx_model_eval M x1))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Var s T) => (__smtx_model_lookup M s T)
  | (SmtTerm.UConst s T) => (__smtx_model_lookup M s T)
  | x1 => SmtValue.NotValue




inductive smt_interprets : SmtModel -> SmtTerm -> Bool -> Prop
  | intro_true  (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean true) ->
      (smt_interprets M t true)
  | intro_false (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean false)->
      smt_interprets M t false

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, (smt_interprets M t true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, ¬ (smt_interprets M t true))->
      smt_satisfiability t false

/- FIXME inductive smt_model_well_typed : SmtModel -> Prop, based on smt axiom -/

/- ---------------------------------------------- -/

end Smtm
