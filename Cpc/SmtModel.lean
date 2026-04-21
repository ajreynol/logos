import Cpc.SmtEval

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

/- SMT literal evaluation defined -/

abbrev native_Char := Char

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
abbrev native_RegLan := SmtRegLan
  
-- SMT Beyond Eunoia

def native_int_log2 : native_Int -> native_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))
  
def native_str_lt : native_String -> native_String -> native_Bool
  | s₁, s₂ => decide (s₁ < s₂)
def native_str_from_int : native_Int -> native_String
  | i => if i < 0 then "" else (toString i)
def native_str_to_int : native_String -> native_Int
  | s => match s.toList with
          | [] => -1
          | '0' :: _ :: _ => -1
          | cs => s.toInt?.getD (-1)
def native_str_to_upper : native_String -> native_String
  | s => s.toUpper
def native_str_to_lower : native_String -> native_String
  | s => s.toLower

-- Regular expressions

def native_re_nullable : native_RegLan -> native_Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => native_re_nullable r₁ && native_re_nullable r₂
  | .union r₁ r₂ => native_re_nullable r₁ || native_re_nullable r₂
  | .inter r₁ r₂ => native_re_nullable r₁ && native_re_nullable r₂
  | .star _ => true
  | .comp r => !(native_re_nullable r)

def native_re_mk_concat (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def native_re_mk_union (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def native_re_mk_inter (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def native_re_mk_comp : native_RegLan -> native_RegLan
  | .comp r => r
  | r => .comp r

def native_re_mk_star : native_RegLan -> native_RegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

def native_re_deriv (c : Char) : native_RegLan -> native_RegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if lo.toNat <= c.toNat && c.toNat <= hi.toNat then .epsilon else .empty
  | .allchar => .epsilon
  | .concat r₁ r₂ =>
      native_re_mk_union
        (native_re_mk_concat (native_re_deriv c r₁) r₂)
        (if native_re_nullable r₁ then native_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => native_re_mk_union (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .inter r₁ r₂ => native_re_mk_inter (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .star r => native_re_mk_concat (native_re_deriv c r) (.star r)
  | .comp r => native_re_mk_comp (native_re_deriv c r)

def native_re_of_list : List Char -> native_RegLan
  | [] => .epsilon
  | c :: cs => native_re_mk_concat (.char c) (native_re_of_list cs)

def native_re_prefix_match_len? (r : native_RegLan) (xs : List Char) : Option Nat :=
  let rec go (cur : native_RegLan) (rest : List Char) (n : Nat) : Option Nat :=
    if native_re_nullable cur then
      some n
    else
      match rest with
      | [] => none
      | c :: cs => go (native_re_deriv c cur) cs (n + 1)
  go r xs 0

def native_re_find_idx_aux (r : native_RegLan) (xs : List Char) (idx : Nat) : Option (Nat × Nat) :=
  match native_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_idx_aux r cs (idx + 1)

def native_re_find_idx_from (r : native_RegLan) (xs : List Char) (start : Nat) : Option (Nat × Nat) :=
  native_re_find_idx_aux r (xs.drop start) start

def native_re_replace_all_list_aux (fuel : Nat) (r : native_RegLan) (replacement : List Char) :
    List Char -> List Char
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match native_re_prefix_match_len? r xs with
          | some 0 =>
              match xs with
              | [] => replacement
              | c :: cs => replacement ++ (c :: native_re_replace_all_list_aux fuel r replacement cs)
          | some (n + 1) =>
              replacement ++ native_re_replace_all_list_aux fuel r replacement (xs.drop (n + 1))
          | none =>
              match xs with
              | [] => []
              | c :: cs => c :: native_re_replace_all_list_aux fuel r replacement cs

def native_re_replace_all_list (r : native_RegLan) (replacement xs : List Char) : List Char :=
  native_re_replace_all_list_aux (xs.length + 1) r replacement xs

def native_str_to_re : native_String -> native_RegLan
  | s => native_re_of_list s.toList
def native_re_mult : native_RegLan -> native_RegLan
  | r => native_re_mk_star r
def native_re_plus : native_RegLan -> native_RegLan
  | r => native_re_mk_concat r (native_re_mk_star r)
def native_re_comp : native_RegLan -> native_RegLan
  | r => native_re_mk_comp r
def native_re_concat : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_concat r₁ r₂
def native_re_inter : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_inter r₁ r₂
def native_re_diff : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_inter r₁ (native_re_mk_comp r₂)
def native_re_union : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_union r₁ r₂
def native_re_range : native_String -> native_String -> native_RegLan
  | s₁, s₂ =>
      match s₁.toList, s₂.toList with
      | [c₁], [c₂] => .range c₁ c₂
      | _, _ => .empty
def native_str_in_re : native_String -> native_RegLan -> native_Bool
  | s, r =>
      native_re_nullable <| s.toList.foldl (fun acc c => native_re_deriv c acc) r
def native_str_indexof_re : native_String -> native_RegLan -> native_Int -> native_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        match native_re_find_idx_from r s.toList (Int.toNat i) with
        | some (idx, _) => Int.ofNat idx
        | none => -1
def native_str_replace_re : native_String -> native_RegLan -> native_String -> native_String
  | s, r, replacement =>
      match native_re_find_idx_from r s.toList 0 with
      | some (idx, len) =>
          String.ofList <| (s.toList.take idx) ++ replacement.toList ++ (s.toList.drop (idx + len))
      | none => s
def native_str_replace_re_all : native_String -> native_RegLan -> native_String -> native_String
  | s, r, replacement => String.ofList <| native_re_replace_all_list r replacement.toList s.toList
def native_re_allchar : native_RegLan := .allchar
def native_re_none : native_RegLan := .empty
def native_re_all : native_RegLan := .star .allchar

-- Partial semantics

def native_qdiv_by_zero_id : native_String := "@qdiv_by_zero"
def native_div_by_zero_id : native_String := "@div_by_zero"
def native_mod_by_zero_id : native_String := "@mod_by_zero"
def native_wrong_apply_sel_id : native_String := "@wrong_apply_sel"
def native_oob_seq_nth_id : native_String := "@oob_seq_nth"
def native_uconst_id : native_Nat -> native_String
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
  | BitVec : native_Nat -> SmtType
  | Map : SmtType -> SmtType -> SmtType
  | Set : SmtType -> SmtType
  | Seq : SmtType -> SmtType
  | Char : SmtType
  | Datatype : native_String -> SmtDatatype -> SmtType
  | TypeRef : native_String -> SmtType
  | USort : native_Nat -> SmtType
  | FunType : SmtType -> SmtType -> SmtType
  | DtcAppType : SmtType -> SmtType -> SmtType

deriving Repr, DecidableEq, Inhabited

/- 
Ordinary SMT-LIB theory operators.
-/
inductive SmtTheoryOp : Type where
  | not : SmtTheoryOp
  | or : SmtTheoryOp
  | and : SmtTheoryOp
  | imp : SmtTheoryOp
  | xor : SmtTheoryOp
  | plus : SmtTheoryOp
  | neg : SmtTheoryOp
  | mult : SmtTheoryOp
  | lt : SmtTheoryOp
  | leq : SmtTheoryOp
  | gt : SmtTheoryOp
  | geq : SmtTheoryOp
  | to_real : SmtTheoryOp
  | to_int : SmtTheoryOp
  | is_int : SmtTheoryOp
  | abs : SmtTheoryOp
  | uneg : SmtTheoryOp
  | div : SmtTheoryOp
  | mod : SmtTheoryOp
  | multmult : SmtTheoryOp
  | divisible : SmtTheoryOp
  | int_pow2 : SmtTheoryOp
  | int_log2 : SmtTheoryOp
  | div_total : SmtTheoryOp
  | mod_total : SmtTheoryOp
  | multmult_total : SmtTheoryOp
  | select : SmtTheoryOp
  | store : SmtTheoryOp
  | concat : SmtTheoryOp
  | extract : SmtTheoryOp
  | repeat : SmtTheoryOp
  | bvnot : SmtTheoryOp
  | bvand : SmtTheoryOp
  | bvor : SmtTheoryOp
  | bvnand : SmtTheoryOp
  | bvnor : SmtTheoryOp
  | bvxor : SmtTheoryOp
  | bvxnor : SmtTheoryOp
  | bvcomp : SmtTheoryOp
  | bvneg : SmtTheoryOp
  | bvadd : SmtTheoryOp
  | bvmul : SmtTheoryOp
  | bvudiv : SmtTheoryOp
  | bvurem : SmtTheoryOp
  | bvsub : SmtTheoryOp
  | bvsdiv : SmtTheoryOp
  | bvsrem : SmtTheoryOp
  | bvsmod : SmtTheoryOp
  | bvult : SmtTheoryOp
  | bvule : SmtTheoryOp
  | bvugt : SmtTheoryOp
  | bvuge : SmtTheoryOp
  | bvslt : SmtTheoryOp
  | bvsle : SmtTheoryOp
  | bvsgt : SmtTheoryOp
  | bvsge : SmtTheoryOp
  | bvshl : SmtTheoryOp
  | bvlshr : SmtTheoryOp
  | bvashr : SmtTheoryOp
  | zero_extend : SmtTheoryOp
  | sign_extend : SmtTheoryOp
  | rotate_left : SmtTheoryOp
  | rotate_right : SmtTheoryOp
  | bvuaddo : SmtTheoryOp
  | bvnego : SmtTheoryOp
  | bvsaddo : SmtTheoryOp
  | bvumulo : SmtTheoryOp
  | bvsmulo : SmtTheoryOp
  | bvusubo : SmtTheoryOp
  | bvssubo : SmtTheoryOp
  | bvsdivo : SmtTheoryOp
  | str_len : SmtTheoryOp
  | str_concat : SmtTheoryOp
  | str_substr : SmtTheoryOp
  | str_contains : SmtTheoryOp
  | str_replace : SmtTheoryOp
  | str_indexof : SmtTheoryOp
  | str_at : SmtTheoryOp
  | str_prefixof : SmtTheoryOp
  | str_suffixof : SmtTheoryOp
  | str_rev : SmtTheoryOp
  | str_update : SmtTheoryOp
  | str_to_lower : SmtTheoryOp
  | str_to_upper : SmtTheoryOp
  | str_to_code : SmtTheoryOp
  | str_from_code : SmtTheoryOp
  | str_is_digit : SmtTheoryOp
  | str_to_int : SmtTheoryOp
  | str_from_int : SmtTheoryOp
  | str_lt : SmtTheoryOp
  | str_leq : SmtTheoryOp
  | str_replace_all : SmtTheoryOp
  | str_replace_re : SmtTheoryOp
  | str_replace_re_all : SmtTheoryOp
  | str_indexof_re : SmtTheoryOp
  | re_allchar : SmtTheoryOp
  | re_none : SmtTheoryOp
  | re_all : SmtTheoryOp
  | str_to_re : SmtTheoryOp
  | re_mult : SmtTheoryOp
  | re_plus : SmtTheoryOp
  | re_exp : SmtTheoryOp
  | re_opt : SmtTheoryOp
  | re_comp : SmtTheoryOp
  | re_range : SmtTheoryOp
  | re_concat : SmtTheoryOp
  | re_inter : SmtTheoryOp
  | re_union : SmtTheoryOp
  | re_diff : SmtTheoryOp
  | re_loop : SmtTheoryOp
  | str_in_re : SmtTheoryOp
  | seq_unit : SmtTheoryOp
  | seq_nth : SmtTheoryOp
  | set_singleton : SmtTheoryOp
  | set_union : SmtTheoryOp
  | set_inter : SmtTheoryOp
  | set_minus : SmtTheoryOp
  | set_member : SmtTheoryOp
  | set_subset : SmtTheoryOp
  | qdiv : SmtTheoryOp
  | qdiv_total : SmtTheoryOp
  | int_to_bv : SmtTheoryOp
  | ubv_to_int : SmtTheoryOp
  | sbv_to_int : SmtTheoryOp

deriving Repr, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | TheoryOp : SmtTheoryOp -> SmtTerm
  | None : SmtTerm
  | Boolean : native_Bool -> SmtTerm
  | Numeral : native_Int -> SmtTerm
  | Rational : native_Rat -> SmtTerm
  | String : native_String -> SmtTerm
  | Binary : native_Int -> native_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : native_String -> SmtType -> SmtTerm
  | ite : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | eq : SmtTerm -> SmtTerm -> SmtTerm
  | exists : native_String -> SmtType -> SmtTerm -> SmtTerm
  | forall : native_String -> SmtType -> SmtTerm -> SmtTerm
  | choice_nth : native_String -> SmtType -> SmtTerm -> native_Nat -> SmtTerm
  | DtCons : native_String -> SmtDatatype -> native_Nat -> SmtTerm
  | DtSel : native_String -> SmtDatatype -> native_Nat -> native_Nat -> SmtTerm
  | DtTester : native_String -> SmtDatatype -> native_Nat -> SmtTerm
  | UConst : native_String -> SmtType -> SmtTerm
  | seq_empty : SmtType -> SmtTerm
  | set_empty : SmtType -> SmtTerm

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
  | Fun : SmtMap -> SmtValue
  | Set : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | Char : native_Char -> SmtValue
  | UValue : native_Nat -> native_Nat -> SmtValue
  | RegLan : native_RegLan -> SmtValue
  | DtCons : native_String -> SmtDatatype -> native_Nat -> SmtValue
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

/-- A bare SMT theory operator viewed as a term. -/
def theory0 (op : SmtTheoryOp) : SmtTerm :=
  SmtTerm.TheoryOp op

/-- Applies a unary SMT theory operator to one argument. -/
def theory1 (op : SmtTheoryOp) (t : SmtTerm) : SmtTerm :=
  SmtTerm.Apply (theory0 op) t

/-- Applies a binary SMT theory operator to two arguments. -/
def theory2 (op : SmtTheoryOp) (t1 t2 : SmtTerm) : SmtTerm :=
  SmtTerm.Apply (theory1 op t1) t2

/-- Applies a ternary SMT theory operator to three arguments. -/
def theory3 (op : SmtTheoryOp) (t1 t2 t3 : SmtTerm) : SmtTerm :=
  SmtTerm.Apply (theory2 op t1 t2) t3


/- SMT-LIB model -/
structure SmtModelKey where
  name : native_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

abbrev SmtModel := SmtModelKey -> Option SmtValue

def SmtModel.empty : SmtModel :=
  fun _ => none

def __smtx_model_key (s : native_String) (T : SmtType) : SmtModelKey :=
  { name := s, ty := T }

def __smtx_model_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  match M (__smtx_model_key s T) with
  | some v => v
  | none => SmtValue.NotValue

def __smtx_model_push (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  fun k =>
    if k = (__smtx_model_key s T) then
      some v
    else
      M k

abbrev RefList := List native_String

def native_reflist_nil : RefList := []
def native_reflist_insert (xs : RefList) (s : native_String) := (s :: xs)
def native_reflist_contains (xs : RefList) (s : native_String ) :=
  decide (s ∈ xs)

/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)
/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

macro_rules
  | `(native_veq_ext $m1 $m2) => do
      let lookupId := Lean.mkIdent `__smtx_msm_lookup
      `(by
          classical
          exact
            if hExt :
                ∀ v : SmtValue,
                  $lookupId $m1 v = $lookupId $m2 v then
              true
            else
              false)
  | `(native_eval_texists $M $s $T $body) => do
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
  | `(native_eval_tforall $M $s $T $body) => do
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
  | `(native_eval_tchoice $M $s $T $body) => do
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
  | `(native_eval_tchoice_nth $M $s $T $body $n) => do
      let evalChoiceId := Lean.mkIdent `native_eval_tchoice
      let pushId := Lean.mkIdent `__smtx_model_push
      `(by
          classical
          let rec evalChoiceNth (M' : SmtModel)
              (s' : native_String) (T' : SmtType) (body' : SmtTerm) : native_Nat -> SmtValue
            | native_nat_zero =>
                $evalChoiceId M' s' T' body'
            | native_nat_succ n' =>
                let v := $evalChoiceId M' s' T' body'
                match body' with
                | SmtTerm.exists s'' T'' body'' =>
                    evalChoiceNth ($pushId M' s' T' v) s'' T'' body'' n'
                | _ => SmtValue.NotValue
          exact evalChoiceNth $M $s $T $body $n)

/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

def native_inhabited_type (T : SmtType) : native_Bool := by
  classical
  exact decide (∃ v : SmtValue, __smtx_typeof_value v = T)

def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


def __vsm_apply_arg_nth : SmtValue -> native_Nat -> native_Nat -> SmtValue
  | (SmtValue.Apply f a), n, (native_nat_succ npos) => (native_ite (native_nateq n npos) a (__vsm_apply_arg_nth f n npos))
  | a, n, npos => SmtValue.NotValue


def __smtx_dt_cons_wf_rec : SmtDatatypeCons -> RefList -> native_Bool
  | (SmtDatatypeCons.cons (SmtType.TypeRef s) c), refs => (native_ite (native_reflist_contains refs s) (__smtx_dt_cons_wf_rec c refs) false)
  | (SmtDatatypeCons.cons T c), refs => (native_ite (__smtx_type_wf_rec T refs) (__smtx_dt_cons_wf_rec c refs) false)
  | SmtDatatypeCons.unit, refs => true


def __smtx_dt_wf_rec : SmtDatatype -> RefList -> native_Bool
  | SmtDatatype.null, refs => true
  | (SmtDatatype.sum c d), refs => (native_ite (__smtx_dt_cons_wf_rec c refs) (__smtx_dt_wf_rec d refs) false)


def __smtx_type_wf_rec : SmtType -> RefList -> native_Bool
  | (SmtType.Datatype s d), refs => (__smtx_dt_wf_rec d (native_reflist_insert refs s))
  | (SmtType.TypeRef s), refs => false
  | (SmtType.Seq x1), refs => (__smtx_type_wf_rec x1 native_reflist_nil)
  | (SmtType.Map x1 x2), refs => (native_and (__smtx_type_wf_rec x1 native_reflist_nil) (__smtx_type_wf_rec x2 native_reflist_nil))
  | (SmtType.FunType x1 x2), refs => (native_and (__smtx_type_wf_rec x1 native_reflist_nil) (__smtx_type_wf_rec x2 native_reflist_nil))
  | (SmtType.Set x1), refs => (__smtx_type_wf_rec x1 native_reflist_nil)
  | (SmtType.DtcAppType x1 x2), refs => false
  | SmtType.None, refs => false
  | T, refs => true


def __smtx_type_wf (T : SmtType) : native_Bool :=
  (__smtx_type_wf_rec T native_reflist_nil)

def __smtx_typeof_guard (T : SmtType) (U : SmtType) : SmtType :=
  (native_ite (native_Teq T SmtType.None) SmtType.None U)

def __smtx_typeof_guard_wf (T : SmtType) (U : SmtType) : SmtType :=
  (native_ite (native_inhabited_type T) (native_ite (__smtx_type_wf T) U SmtType.None) SmtType.None)

def __smtx_msm_get_default : SmtMap -> SmtValue
  | (SmtMap.cons j e m) => (__smtx_msm_get_default m)
  | (SmtMap.default T e) => e


def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (native_ite (native_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => 
    let _v0 := (__smtx_typeof_map_value m)
    (native_ite (native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) _v0) _v0 SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


def __smtx_index_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => T
  | T => SmtType.None


def __smtx_elem_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => U
  | T => SmtType.None


def __smtx_mss_op_internal (isInter : native_Bool) : SmtMap -> SmtMap -> SmtMap -> SmtMap
  | (SmtMap.default T efalse), m2, acc => acc
  | (SmtMap.cons e etrue m1), m2, acc => 
    let _v0 := (SmtValue.Boolean true)
    (__smtx_mss_op_internal isInter m1 m2 (native_ite (native_iff (native_veq (__smtx_msm_lookup m2 e) _v0) isInter) (SmtMap.cons e _v0 acc) acc))


def __smtx_map_to_set_type : SmtType -> SmtType
  | (SmtType.Map T SmtType.Bool) => (SmtType.Set T)
  | T => SmtType.None


def __smtx_map_to_fun_type : SmtType -> SmtType
  | (SmtType.Map T U) => (SmtType.FunType T U)
  | T => SmtType.None


def __smtx_ssm_seq_nth : SmtSeq -> native_Int -> SmtValue -> SmtValue
  | (SmtSeq.empty T), n, d => d
  | (SmtSeq.cons v vs), 0, d => v
  | (SmtSeq.cons v vs), n, d => (__smtx_ssm_seq_nth vs (native_zplus n (native_zneg 1)) d)


def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => 
    let _v0 := (__smtx_typeof_seq_value vs)
    (native_ite (native_Teq (SmtType.Seq (__smtx_typeof_value v)) _v0) _v0 SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


def __smtx_elem_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => (__smtx_elem_typeof_seq_value vs)
  | (SmtSeq.empty T) => T


def __smtx_dtc_concat : SmtDatatypeCons -> SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons U c1), c2 => (SmtDatatypeCons.cons U (__smtx_dtc_concat c1 c2))
  | SmtDatatypeCons.unit, c2 => c2


def __smtx_dtc_num_sels : SmtDatatypeCons -> native_Nat
  | (SmtDatatypeCons.cons U c) => (native_nat_succ (__smtx_dtc_num_sels c))
  | SmtDatatypeCons.unit => native_nat_zero


def __smtx_dt_num_sels : SmtDatatype -> native_Nat -> native_Nat
  | (SmtDatatype.sum c d), native_nat_zero => (__smtx_dtc_num_sels c)
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_dt_num_sels d n)
  | SmtDatatype.null, n => native_nat_zero


def __smtx_dtc_substitute (s : native_String) (d : SmtDatatype) : SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons (SmtType.Datatype s2 d2) c) => (SmtDatatypeCons.cons (SmtType.Datatype s2 (native_ite (native_streq s s2) d2 (__smtx_dt_substitute s d d2))) (__smtx_dtc_substitute s d c))
  | (SmtDatatypeCons.cons T c) => (SmtDatatypeCons.cons (native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T) (__smtx_dtc_substitute s d c))
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit


def __smtx_dt_substitute (s : native_String) (d : SmtDatatype) : SmtDatatype -> SmtDatatype
  | (SmtDatatype.sum c d2) => (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d2))
  | SmtDatatype.null => SmtDatatype.null


def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> native_Nat -> SmtType
  | (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => (SmtType.DtcAppType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero))
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_typeof_dt_cons_value_rec T d n)
  | d, n => SmtType.None


def __smtx_typeof_dt_cons_rec (T : SmtType) : SmtDatatype -> native_Nat -> SmtType
  | (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => (SmtType.DtcAppType U (__smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero))
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_typeof_dt_cons_rec T d n)
  | d, n => SmtType.None


def __smtx_ret_typeof_sel_rec : SmtDatatype -> native_Nat -> native_Nat -> SmtType
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, (native_nat_succ m) => (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero m)
  | (SmtDatatype.sum c d), (native_nat_succ n), m => (__smtx_ret_typeof_sel_rec d n m)
  | d, n, m => SmtType.None


def __smtx_ret_typeof_sel (s : native_String) (d : SmtDatatype) (n : native_Nat) (m : native_Nat) : SmtType :=
  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) n m)

def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtcAppType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.Binary w n) => (native_ite (native_zleq 0 w) (SmtType.BitVec (native_int_to_nat w)) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Set m) => (__smtx_map_to_set_type (__smtx_typeof_map_value m))
  | (SmtValue.Fun m) => (__smtx_map_to_fun_type (__smtx_typeof_map_value m))
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.Char c) => SmtType.Char
  | (SmtValue.UValue i e) => (SmtType.USort i)
  | (SmtValue.DtCons s d i) => 
    let _v0 := (SmtType.Datatype s d)
    (native_ite (__smtx_type_wf _v0) (__smtx_typeof_dt_cons_value_rec _v0 (__smtx_dt_substitute s d d) i) SmtType.None)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), t2, t3 => t2
  | (SmtValue.Boolean false), t2, t3 => t3
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Boolean (native_veq_ext m1 m2))
  | (SmtValue.Set m1), (SmtValue.Set m2) => (SmtValue.Boolean (native_veq_ext m1 m2))
  | (SmtValue.Fun m1), (SmtValue.Fun m2) => (SmtValue.Boolean (native_veq_ext m1 m2))
  | (SmtValue.Seq (SmtSeq.empty T1)), (SmtValue.Seq (SmtSeq.empty T2)) => (SmtValue.Boolean true)
  | (SmtValue.Seq (SmtSeq.cons v1 vs1)), (SmtValue.Seq (SmtSeq.cons v2 vs2)) => 
    let _v0 := (SmtValue.Boolean true)
    (SmtValue.Boolean (native_and (native_veq (__smtx_model_eval_eq v1 v2) _v0) (native_veq (__smtx_model_eval_eq (SmtValue.Seq vs1) (SmtValue.Seq vs2)) _v0)))
  | (SmtValue.Apply f1 v1), (SmtValue.Apply f2 v2) => 
    let _v0 := (SmtValue.Boolean true)
    (SmtValue.Boolean (native_and (native_veq (__smtx_model_eval_eq f1 f2) _v0) (native_veq (__smtx_model_eval_eq v1 v2) _v0)))
  | v1, v2 => (SmtValue.Boolean (native_veq v1 v2))


def __smtx_map_select : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i => (__smtx_msm_lookup m i)
  | (SmtValue.Set m), i => (__smtx_msm_lookup m i)
  | v, i => SmtValue.NotValue


def __smtx_map_store : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i, e => (SmtValue.Map (SmtMap.cons i e m))
  | (SmtValue.Set m), i, e => (SmtValue.Set (SmtMap.cons i e m))
  | v, i, e => SmtValue.NotValue


def __smtx_set_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Set m1), (SmtValue.Set m2) => (SmtValue.Set (__smtx_mss_op_internal true m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


def __smtx_set_minus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Set m1), (SmtValue.Set m2) => (SmtValue.Set (__smtx_mss_op_internal false m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


def __smtx_set_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Set m1), (SmtValue.Set m2) => (SmtValue.Set (__smtx_mss_op_internal false m1 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false)) m2))
  | v1, v2 => SmtValue.NotValue


def __smtx_seq_nth_wrong (M : SmtModel) (s : SmtSeq) (n : native_Int) : SmtType -> SmtValue
  | (SmtType.Seq T) => (__smtx_map_select (__smtx_map_select (__smtx_model_lookup M native_oob_seq_nth_id (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T))) (SmtValue.Seq s)) (SmtValue.Numeral n))
  | T => SmtValue.NotValue


def __smtx_seq_nth (M : SmtModel) : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq s), (SmtValue.Numeral n) => (__smtx_ssm_seq_nth s n (__smtx_seq_nth_wrong M s n (__smtx_typeof_seq_value s)))
  | v1, v2 => SmtValue.NotValue


def __smtx_bv_sizeof_type : SmtType -> native_Int
  | (SmtType.BitVec x1) => (native_nat_to_int x1)
  | t1 => (native_zneg 1)


def __smtx_bv_sizeof_value : SmtValue -> native_Int
  | (SmtValue.Binary x1 x2) => x1
  | t1 => (native_zneg 1)


def __smtx_model_eval_dt_sel (M : SmtModel) (s : native_String) (d : SmtDatatype) (n : native_Nat) (m : native_Nat) (v : SmtValue) : SmtValue :=
  (native_ite (native_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)) (__vsm_apply_arg_nth v m (__smtx_dt_num_sels d n)) (__smtx_map_select (__smtx_map_select (__smtx_map_select (__smtx_model_lookup M native_wrong_apply_sel_id (SmtType.Map SmtType.Int (SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m))))) (SmtValue.Numeral (native_nat_to_int n))) (SmtValue.Numeral (native_nat_to_int m))) v))

def __smtx_model_eval_dt_tester (s : native_String) (d : SmtDatatype) (n : native_Nat) (v1 : SmtValue) : SmtValue :=
  (SmtValue.Boolean (native_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n)))

def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | v, SmtValue.NotValue => SmtValue.NotValue
  | (SmtValue.DtCons s d n), i => (SmtValue.Apply (SmtValue.DtCons s d n) i)
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Fun m), i => (__smtx_map_select (SmtValue.Map m) i)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (native_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (native_or x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (native_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_imp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_not x1) x2)

def __smtx_model_eval_xor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_not (__smtx_model_eval_eq x1 x2))

def __smtx_model_eval_plus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_zplus x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (native_qplus x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval__ : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_zplus x1 (native_zneg x2)))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (native_qplus x3 (native_qneg x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_mult : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_zmult x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (native_qmult x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (native_zlt x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (native_qlt x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_leq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (native_zleq x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (native_qleq x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_gt (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_lt x2 x1)

def __smtx_model_eval_geq (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_leq x2 x1)

def __smtx_model_eval_to_real : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Rational (native_to_real x1))
  | (SmtValue.Rational x2) => (SmtValue.Rational x2)
  | t1 => SmtValue.NotValue


def __smtx_model_eval_to_int : SmtValue -> SmtValue
  | (SmtValue.Rational x1) => (SmtValue.Numeral (native_to_int x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_is_int (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq (__smtx_model_eval_to_real (__smtx_model_eval_to_int x1)) x1)

def __smtx_model_eval_abs (x1 : SmtValue) : SmtValue :=
  
    let _v0 := (SmtValue.Numeral 0)
    (__smtx_model_eval_ite (__smtx_model_eval_lt x1 _v0) (__smtx_model_eval__ _v0 x1) x1)

def __smtx_model_eval_uneg : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (native_zneg x1))
  | (SmtValue.Rational x2) => (SmtValue.Rational (native_qneg x2))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_divisible (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq (__smtx_model_eval_mod_total x2 x1) (SmtValue.Numeral 0))

def __smtx_model_eval_int_pow2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (native_int_pow2 x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_int_log2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (native_int_log2 x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_div_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_div_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_mod_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_mod_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_multmult_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (native_zexp_total x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_select (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_map_select x1 x2)

def __smtx_model_eval_store (x1 : SmtValue) (x2 : SmtValue) (x3 : SmtValue) : SmtValue :=
  (__smtx_map_store x1 x2 x3)

def __smtx_model_eval_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (native_zplus x1 x3)
    (SmtValue.Binary _v0 (native_mod_total (native_binary_concat x1 x2 x3 x4) (native_int_pow2 _v0)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_extract : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (native_zplus (native_zplus x1 1) (native_zneg x2))
    (SmtValue.Binary _v0 (native_mod_total (native_binary_extract x3 x4 x1 x2) (native_int_pow2 _v0)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_repeat_rec : native_Nat -> SmtValue -> SmtValue
  | native_nat_zero, x1 => (SmtValue.Binary 0 0)
  | (native_nat_succ n), x1 => (__smtx_model_eval_concat x1 (__smtx_model_eval_repeat_rec n x1))


def __smtx_model_eval_repeat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (__smtx_model_eval_repeat_rec (native_int_to_nat x1) (SmtValue.Binary x2 x3))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnot : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (native_mod_total (native_binary_not x1 x2) (native_int_pow2 x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvand : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_binary_and x1 x2 x4) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_binary_or x1 x2 x4) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnand (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvand x1 x2))

def __smtx_model_eval_bvnor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvor x1 x2))

def __smtx_model_eval_bvxor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_binary_xor x1 x2 x4) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvxnor (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvnot (__smtx_model_eval_bvxor x1 x2))

def __smtx_model_eval_bvcomp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_ite (__smtx_model_eval_eq x1 x2) (SmtValue.Binary 1 1) (SmtValue.Binary 1 0))

def __smtx_model_eval_bvneg : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (native_mod_total (native_zneg x2) (native_int_pow2 x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvadd : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_zplus x2 x4) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvmul : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_zmult x2 x4) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvudiv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_ite (native_zeq x4 0) (native_binary_max x1) (native_div_total x2 x4)) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvurem : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_ite (native_zeq x4 0) x2 (native_mod_total x2 x4)) (native_int_pow2 x1)))
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
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (native_zlt x4 x2))
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
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_zmult x2 (native_int_pow2 x4)) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvlshr : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary x1 (native_mod_total (native_div_total x2 (native_int_pow2 x4)) (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvashr (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v1 := (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value x1)) (SmtValue.Numeral 1))
    (__smtx_model_eval_ite (__smtx_model_eval_eq (__smtx_model_eval_extract _v1 _v1 x1) (SmtValue.Binary 1 0)) (__smtx_model_eval_bvlshr x1 x2) (__smtx_model_eval_bvnot (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot x1) x2)))

def __smtx_model_eval_zero_extend : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (SmtValue.Binary (native_zplus x1 x2) x3)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_sign_extend : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => 
    let _v0 := (native_zplus x1 x2)
    (SmtValue.Binary _v0 (native_mod_total (native_binary_uts x2 x3) (native_int_pow2 _v0)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_rotate_left_rec : native_Nat -> SmtValue -> SmtValue
  | native_nat_zero, (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 x2)
  | (native_nat_succ n), (SmtValue.Binary x1 x2) => 
    let _v0 := (SmtValue.Binary x1 x2)
    let _v1 := (native_zneg 1)
    let _v2 := (native_zplus x1 _v1)
    let _v3 := (SmtValue.Numeral _v2)
    (__smtx_model_eval_rotate_left_rec n (__smtx_model_eval_concat (__smtx_model_eval_extract (SmtValue.Numeral (native_zplus _v2 _v1)) (SmtValue.Numeral 0) _v0) (__smtx_model_eval_extract _v3 _v3 _v0)))
  | n, t1 => SmtValue.NotValue


def __smtx_model_eval_rotate_left : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), x2 => (__smtx_model_eval_rotate_left_rec (native_int_to_nat x1) x2)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_rotate_right_rec : native_Nat -> SmtValue -> SmtValue
  | native_nat_zero, (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 x2)
  | (native_nat_succ n), (SmtValue.Binary x1 x2) => 
    let _v0 := (SmtValue.Binary x1 x2)
    let _v2 := (SmtValue.Numeral 0)
    (__smtx_model_eval_rotate_right_rec n (__smtx_model_eval_concat (__smtx_model_eval_extract _v2 _v2 _v0) (__smtx_model_eval_extract (SmtValue.Numeral (native_zplus x1 (native_zneg 1))) (SmtValue.Numeral 1) _v0)))
  | n, t1 => SmtValue.NotValue


def __smtx_model_eval_rotate_right : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), x2 => (__smtx_model_eval_rotate_right_rec (native_int_to_nat x1) x2)
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvuaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (native_zleq (native_int_pow2 x1) (native_zplus x2 x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvnego : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Boolean (native_zeq x2 (native_int_pow2 (native_zplus x1 (native_zneg 1)))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_bvsaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (native_int_pow2 (native_zplus x1 (native_zneg 1)))
    let _v1 := (native_zplus (native_binary_uts x1 x2) (native_binary_uts x3 x4))
    (SmtValue.Boolean (native_or (native_zleq _v0 _v1) (native_zlt _v1 (native_zneg _v0))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvumulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (native_zleq (native_int_pow2 x1) (native_zmult x2 x4)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvsmulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => 
    let _v0 := (native_int_pow2 (native_zplus x1 (native_zneg 1)))
    let _v1 := (native_zmult (native_binary_uts x1 x2) (native_binary_uts x3 x4))
    (SmtValue.Boolean (native_or (native_zleq _v0 _v1) (native_zlt _v1 (native_zneg _v0))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_bvusubo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_bvult x1 x2)

def __smtx_model_eval_bvssubo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_ite (__smtx_model_eval_bvnego x2) (__smtx_model_eval_bvsge x1 (SmtValue.Binary (__smtx_bv_sizeof_value x1) 0)) (__smtx_model_eval_bvsaddo x1 (__smtx_model_eval_bvneg x2)))

def __smtx_model_eval_bvsdivo (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_and (__smtx_model_eval_bvnego x1) (__smtx_model_eval_eq x2 (__smtx_model_eval_bvnot (SmtValue.Binary (__smtx_bv_sizeof_value x1) 0))))

def __smtx_model_eval_str_len : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (native_seq_len (native_unpack_seq x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_concat (native_unpack_seq x1) (native_unpack_seq x2))))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_substr : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Numeral x2), (SmtValue.Numeral x3) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_extract (native_unpack_seq x1) x2 x3)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_contains : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Boolean (native_seq_contains (native_unpack_seq x1) (native_unpack_seq x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_replace : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Seq x3) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_replace (native_unpack_seq x1) (native_unpack_seq x2) (native_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_indexof : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (native_seq_indexof (native_unpack_seq x1) (native_unpack_seq x2) x3))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_at (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_str_substr x1 x2 (SmtValue.Numeral 1))

def __smtx_model_eval_str_prefixof (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_eq x1 (__smtx_model_eval_str_substr x2 (SmtValue.Numeral 0) (__smtx_model_eval_str_len x1)))

def __smtx_model_eval_str_suffixof (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_str_len x1)
    (__smtx_model_eval_eq x1 (__smtx_model_eval_str_substr x2 (__smtx_model_eval__ (__smtx_model_eval_str_len x2) _v0) _v0))

def __smtx_model_eval_str_rev : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_rev (native_unpack_seq x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_update : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Numeral x2), (SmtValue.Seq x3) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_update (native_unpack_seq x1) x2 (native_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_to_lower : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (native_pack_string (native_str_to_lower (native_unpack_string x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_to_upper : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Seq (native_pack_string (native_str_to_upper (native_unpack_string x1))))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_to_code : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (native_str_to_code (native_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_from_code : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Seq (native_pack_string (native_str_from_code x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_is_digit (x1 : SmtValue) : SmtValue :=
  
    let _v0 := (__smtx_model_eval_str_to_code x1)
    (__smtx_model_eval_and (__smtx_model_eval_leq (SmtValue.Numeral 48) _v0) (__smtx_model_eval_leq _v0 (SmtValue.Numeral 57)))

def __smtx_model_eval_str_to_int : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.Numeral (native_str_to_int (native_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_from_int : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Seq (native_pack_string (native_str_from_int x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_str_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.Boolean (native_str_lt (native_unpack_string x1) (native_unpack_string x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_str_leq (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_eq x1 x2) (__smtx_model_eval_str_lt x1 x2))

def __smtx_model_eval_str_replace_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2), (SmtValue.Seq x3) => (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value x1) (native_seq_replace_all (native_unpack_seq x1) (native_unpack_seq x2) (native_unpack_seq x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_replace_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Seq x3) => (SmtValue.Seq (native_pack_string (native_str_replace_re (native_unpack_string x1) x2 (native_unpack_string x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_replace_re_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Seq x3) => (SmtValue.Seq (native_pack_string (native_str_replace_re_all (native_unpack_string x1) x2 (native_unpack_string x3))))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_indexof_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (native_str_indexof_re (native_unpack_string x1) x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_to_re : SmtValue -> SmtValue
  | (SmtValue.Seq x1) => (SmtValue.RegLan (native_str_to_re (native_unpack_string x1)))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_mult : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (native_re_mult x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_plus (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_re_concat x1 (__smtx_model_eval_re_mult x1))

def __smtx_model_eval_re_exp_rec : native_Nat -> SmtValue -> SmtValue
  | native_nat_zero, x1 => (SmtValue.RegLan (native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))))
  | (native_nat_succ n), x1 => (__smtx_model_eval_re_concat (__smtx_model_eval_re_exp_rec n x1) x1)


def __smtx_model_eval_re_exp : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.RegLan x2) => (__smtx_model_eval_re_exp_rec (native_int_to_nat x1) (SmtValue.RegLan x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_opt (x1 : SmtValue) : SmtValue :=
  (__smtx_model_eval_re_union x1 (SmtValue.RegLan (native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char)))))

def __smtx_model_eval_re_comp : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (native_re_comp x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_re_range : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.Seq x2) => (SmtValue.RegLan (native_re_range (native_unpack_string x1) (native_unpack_string x2)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (native_re_concat x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (native_re_inter x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (native_re_union x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_diff : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (native_re_diff x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_re_loop_rec : native_Nat -> SmtValue -> SmtValue -> SmtValue -> SmtValue
  | native_nat_zero, x1, (SmtValue.Numeral x2), x3 => (__smtx_model_eval_re_exp x1 x3)
  | (native_nat_succ n), x1, (SmtValue.Numeral x2), x3 => (__smtx_model_eval_re_union (__smtx_model_eval_re_loop_rec n x1 (SmtValue.Numeral (native_zplus x2 (native_zneg 1))) x3) (__smtx_model_eval_re_exp (SmtValue.Numeral x2) x3))
  | n, t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_re_loop : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2), (SmtValue.RegLan x3) => 
    let _v0 := (SmtValue.Numeral x2)
    let _v1 := (SmtValue.Numeral x1)
    (__smtx_model_eval_ite (__smtx_model_eval_gt _v1 _v0) (SmtValue.RegLan native_re_none) (__smtx_model_eval_re_loop_rec (native_int_to_nat (native_zplus x2 (native_zneg x1))) _v1 _v0 (SmtValue.RegLan x3)))
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_str_in_re : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq x1), (SmtValue.RegLan x2) => (SmtValue.Boolean (native_str_in_re (native_unpack_string x1) x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_set_singleton (x1 : SmtValue) : SmtValue :=
  (SmtValue.Set (SmtMap.cons x1 (SmtValue.Boolean true) (SmtMap.default (__smtx_typeof_value x1) (SmtValue.Boolean false))))

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
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Rational (native_mk_rational x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (native_qdiv_total x3 x4))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_int_to_bv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Binary x1 (native_mod_total x2 (native_int_pow2 x1)))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_ubv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral x2)
  | t1 => SmtValue.NotValue


def __smtx_model_eval_sbv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral (native_binary_uts x1 x2))
  | t1 => SmtValue.NotValue


def __smtx_typeof_ite : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Bool, U, V => (native_ite (native_Teq U V) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_eq (T : SmtType) (U : SmtType) : SmtType :=
  (__smtx_typeof_guard T (native_ite (native_Teq T U) SmtType.Bool SmtType.None))

def __smtx_typeof_apply : SmtType -> SmtType -> SmtType
  | (SmtType.FunType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | (SmtType.DtcAppType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_choice_nth (T : SmtType) : SmtTerm -> native_Nat -> SmtType
  | F, native_nat_zero => (native_ite (native_Teq (__smtx_typeof F) SmtType.Bool) (__smtx_typeof_guard_wf T T) SmtType.None)
  | (SmtTerm.exists s U F), (native_nat_succ n) => (__smtx_typeof_choice_nth U F n)
  | F, n => SmtType.None


def __smtx_typeof_bv_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n1), (SmtType.BitVec n2) => (native_ite (native_nateq n1 n2) (SmtType.BitVec n1) SmtType.None)
  | T, U => SmtType.None


def __smtx_typeof_bv_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n1), (SmtType.BitVec n2), U => (native_ite (native_nateq n1 n2) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_sets_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.Set x1), (SmtType.Set x2) => (native_ite (native_Teq x1 x2) (SmtType.Set x1) SmtType.None)
  | x1, x2 => SmtType.None


def __smtx_typeof_sets_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Set x1), (SmtType.Set x2), T => (native_ite (native_Teq x1 x2) T SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_seq_op_1 : SmtType -> SmtType
  | (SmtType.Seq x1) => (SmtType.Seq x1)
  | x1 => SmtType.None


def __smtx_typeof_seq_op_1_ret : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), x2 => x2
  | x1, x2 => SmtType.None


def __smtx_typeof_seq_op_2 : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2) => (native_ite (native_Teq x1 x2) (SmtType.Seq x1) SmtType.None)
  | x1, x2 => SmtType.None


def __smtx_typeof_seq_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2), T => (native_ite (native_Teq x1 x2) T SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_seq_op_3 : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2), (SmtType.Seq x3) => (native_ite (native_Teq x1 x2) (native_ite (native_Teq x2 x3) (SmtType.Seq x1) SmtType.None) SmtType.None)
  | x1, x2, x3 => SmtType.None


def __smtx_typeof_bv_op_1 : SmtType -> SmtType
  | (SmtType.BitVec n) => (SmtType.BitVec n)
  | T => SmtType.None


def __smtx_typeof_bv_op_1_ret : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec n), T => T
  | T, U => SmtType.None


def __smtx_typeof_arith_overload_op_1 : SmtType -> SmtType
  | SmtType.Int => SmtType.Int
  | SmtType.Real => SmtType.Real
  | T => SmtType.None


def __smtx_typeof_arith_overload_op_2 : SmtType -> SmtType -> SmtType
  | SmtType.Int, SmtType.Int => SmtType.Int
  | SmtType.Real, SmtType.Real => SmtType.Real
  | T, U => SmtType.None


def __smtx_typeof_arith_overload_op_2_ret : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Int, SmtType.Int, T => T
  | SmtType.Real, SmtType.Real, T => T
  | T, U, V => SmtType.None


def __smtx_typeof_select : SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 x2), x3 => (native_ite (native_Teq x1 x3) x2 SmtType.None)
  | x4, x5 => SmtType.None


def __smtx_typeof_store : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Map x1 x2), x3, x4 => (native_ite (native_Teq x1 x3) (native_ite (native_Teq x2 x4) (SmtType.Map x1 x2) SmtType.None) SmtType.None)
  | x5, x6, x7 => SmtType.None


def __smtx_typeof_concat : SmtType -> SmtType -> SmtType
  | (SmtType.BitVec x1), (SmtType.BitVec x2) => (SmtType.BitVec (native_int_to_nat (native_zplus (native_nat_to_int x1) (native_nat_to_int x2))))
  | x3, x4 => SmtType.None


def __smtx_typeof_extract : SmtTerm -> SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtTerm.Numeral x2), (SmtType.BitVec x3) => (native_ite (native_zleq 0 x2) (native_ite (native_zleq x2 x1) (native_ite (native_zlt x1 (native_nat_to_int x3)) (SmtType.BitVec (native_int_to_nat (native_zplus (native_zplus x1 (native_zneg x2)) 1))) SmtType.None) SmtType.None) SmtType.None)
  | x4, x5, x6 => SmtType.None


def __smtx_typeof_repeat : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (native_ite (native_zleq 1 x1) (SmtType.BitVec (native_int_to_nat (native_zmult x1 (native_nat_to_int x2)))) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_zero_extend : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (native_ite (native_zleq 0 x1) (SmtType.BitVec (native_int_to_nat (native_zplus x1 (native_nat_to_int x2)))) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_sign_extend : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (native_ite (native_zleq 0 x1) (SmtType.BitVec (native_int_to_nat (native_zplus x1 (native_nat_to_int x2)))) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_rotate_left : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (native_ite (native_zleq 0 x1) (SmtType.BitVec x2) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_rotate_right : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtType.BitVec x2) => (native_ite (native_zleq 0 x1) (SmtType.BitVec x2) SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_str_substr : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), SmtType.Int, SmtType.Int => (SmtType.Seq x1)
  | x2, x3, x4 => SmtType.None


def __smtx_typeof_str_indexof : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), (SmtType.Seq x2), SmtType.Int => (native_ite (native_Teq x1 x2) SmtType.Int SmtType.None)
  | x3, x4, x5 => SmtType.None


def __smtx_typeof_str_at : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), SmtType.Int => (SmtType.Seq x1)
  | x2, x3 => SmtType.None


def __smtx_typeof_str_update : SmtType -> SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), SmtType.Int, (SmtType.Seq x2) => (native_ite (native_Teq x1 x2) (SmtType.Seq x1) SmtType.None)
  | x3, x4, x5 => SmtType.None


def __smtx_typeof_re_exp : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), SmtType.RegLan => (native_ite (native_zleq 0 x1) SmtType.RegLan SmtType.None)
  | x2, x3 => SmtType.None


def __smtx_typeof_re_loop : SmtTerm -> SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), (SmtTerm.Numeral x2), SmtType.RegLan => (native_ite (native_zleq 0 x1) (native_ite (native_zleq 0 x2) SmtType.RegLan SmtType.None) SmtType.None)
  | x3, x4, x5 => SmtType.None


def __smtx_typeof_seq_nth : SmtType -> SmtType -> SmtType
  | (SmtType.Seq x1), SmtType.Int => (__smtx_typeof_guard_wf x1 x1)
  | x2, x3 => SmtType.None


def __smtx_typeof_set_member : SmtType -> SmtType -> SmtType
  | x1, (SmtType.Set x2) => (native_ite (native_Teq x1 x2) SmtType.Bool SmtType.None)
  | x3, x4 => SmtType.None


def __smtx_typeof_int_to_bv : SmtTerm -> SmtType -> SmtType
  | (SmtTerm.Numeral x1), SmtType.Int => (native_ite (native_zleq 0 x1) (SmtType.BitVec (native_int_to_nat x1)) SmtType.None)
  | x2, x3 => SmtType.None


def __smtx_typeof : SmtTerm -> SmtType
  | (SmtTerm.Boolean b) => SmtType.Bool
  | (SmtTerm.Numeral n) => SmtType.Int
  | (SmtTerm.Rational r) => SmtType.Real
  | (SmtTerm.String s) => (SmtType.Seq SmtType.Char)
  | (SmtTerm.Binary w n) => (native_ite (native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w)))) (SmtType.BitVec (native_int_to_nat w)) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.not) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.xor) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.plus) x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.neg) x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mult) x1) x2) => (__smtx_typeof_arith_overload_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.lt) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.leq) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.gt) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.geq) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_real) x1) => 
    let _v0 := (__smtx_typeof x1)
    (native_ite (native_Teq _v0 SmtType.Int) SmtType.Real (native_ite (native_Teq _v0 SmtType.Real) SmtType.Real SmtType.None))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_int) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Real) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.is_int) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Real) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.abs) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.uneg) x1) => (__smtx_typeof_arith_overload_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.divisible) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_pow2) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_log2) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div_total) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod_total) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult_total) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Int) SmtType.Int SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.select) x1) x2) => (__smtx_typeof_select (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.store) x1) x2) x3) => (__smtx_typeof_store (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.concat) x1) x2) => (__smtx_typeof_concat (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.extract) x1) x2) x3) => (__smtx_typeof_extract x1 x2 (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.repeat) x1) x2) => (__smtx_typeof_repeat x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnot) x1) => (__smtx_typeof_bv_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvand) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvor) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnand) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnor) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxor) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxnor) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvcomp) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) (SmtType.BitVec (native_nat_succ native_nat_zero)))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvneg) x1) => (__smtx_typeof_bv_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvadd) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvmul) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvudiv) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvurem) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsub) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdiv) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsrem) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmod) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvult) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvule) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvugt) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuge) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvslt) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsle) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsgt) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsge) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvshl) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvlshr) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvashr) x1) x2) => (__smtx_typeof_bv_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.zero_extend) x1) x2) => (__smtx_typeof_zero_extend x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.sign_extend) x1) x2) => (__smtx_typeof_sign_extend x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.rotate_left) x1) x2) => (__smtx_typeof_rotate_left x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.rotate_right) x1) x2) => (__smtx_typeof_rotate_right x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuaddo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnego) x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsaddo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvumulo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmulo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvusubo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvssubo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdivo) x1) x2) => (__smtx_typeof_bv_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.seq_empty x1) => (__smtx_typeof_guard_wf x1 (SmtType.Seq x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_len) x1) => (__smtx_typeof_seq_op_1_ret (__smtx_typeof x1) SmtType.Int)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_concat) x1) x2) => (__smtx_typeof_seq_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_substr) x1) x2) x3) => (__smtx_typeof_str_substr (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_contains) x1) x2) => (__smtx_typeof_seq_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace) x1) x2) x3) => (__smtx_typeof_seq_op_3 (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_indexof) x1) x2) x3) => (__smtx_typeof_str_indexof (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_at) x1) x2) => (__smtx_typeof_str_at (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_prefixof) x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_suffixof) x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_rev) x1) => (__smtx_typeof_seq_op_1 (__smtx_typeof x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_update) x1) x2) x3) => (__smtx_typeof_str_update (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_lower) x1) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) _v0 SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_upper) x1) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) _v0 SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_code) x1) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_from_code) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_is_digit) x1) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Bool SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_int) x1) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.Int SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_from_int) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Int) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_lt) x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_leq) x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) _v0) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_all) x1) x2) x3) => (__smtx_typeof_seq_op_3 (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_re) x1) x2) x3) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x3) _v0) _v0 SmtType.None) SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_re_all) x1) x2) x3) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x3) _v0) _v0 SmtType.None) SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_indexof_re) x1) x2) x3) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x3) SmtType.Int) SmtType.Int SmtType.None) SmtType.None) SmtType.None)
  | (SmtTerm.TheoryOp SmtTheoryOp.re_allchar) => SmtType.RegLan
  | (SmtTerm.TheoryOp SmtTheoryOp.re_none) => SmtType.RegLan
  | (SmtTerm.TheoryOp SmtTheoryOp.re_all) => SmtType.RegLan
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_re) x1) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_mult) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_plus) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_exp) x1) x2) => (__smtx_typeof_re_exp x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_opt) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_comp) x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) SmtType.RegLan SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_range) x1) x2) => 
    let _v0 := (SmtType.Seq SmtType.Char)
    (native_ite (native_Teq (__smtx_typeof x1) _v0) (native_ite (native_Teq (__smtx_typeof x2) _v0) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_concat) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_inter) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_union) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_diff) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.RegLan) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.RegLan SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_loop) x1) x2) x3) => (__smtx_typeof_re_loop x1 x2 (__smtx_typeof x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_in_re) x1) x2) => (native_ite (native_Teq (__smtx_typeof x1) (SmtType.Seq SmtType.Char)) (native_ite (native_Teq (__smtx_typeof x2) SmtType.RegLan) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.seq_unit) x1) => 
    let _v0 := (__smtx_typeof x1)
    (native_ite (native_Teq _v0 SmtType.None) SmtType.None (SmtType.Seq _v0))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.seq_nth) x1) x2) => (__smtx_typeof_seq_nth (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.set_empty x1) => (__smtx_typeof_guard_wf x1 (SmtType.Set x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_singleton) x1) => 
    let _v0 := (__smtx_typeof x1)
    (native_ite (native_Teq _v0 SmtType.None) SmtType.None (SmtType.Set _v0))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_union) x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_inter) x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_minus) x1) x2) => (__smtx_typeof_sets_op_2 (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_member) x1) x2) => (__smtx_typeof_set_member (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_subset) x1) x2) => (__smtx_typeof_sets_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Bool)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Real)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv_total) x1) x2) => (__smtx_typeof_arith_overload_op_2_ret (__smtx_typeof x1) (__smtx_typeof x2) SmtType.Real)
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_to_bv) x1) x2) => (__smtx_typeof_int_to_bv x1 (__smtx_typeof x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.ubv_to_int) x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Int)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.sbv_to_int) x1) => (__smtx_typeof_bv_op_1_ret (__smtx_typeof x1) SmtType.Int)
  | (SmtTerm.ite x1 x2 x3) => (__smtx_typeof_ite (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.eq x1 x2) => (__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.exists s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.forall s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.choice_nth s T x1 n) => (__smtx_typeof_choice_nth T x1 n)
  | (SmtTerm.DtCons s d i) => 
    let _v0 := (SmtType.Datatype s d)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_dt_cons_rec _v0 (__smtx_dt_substitute s d d) i))
  | (SmtTerm.Apply (SmtTerm.DtSel s d i j) x1) => 
    let _v0 := (__smtx_ret_typeof_sel s d i j)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) _v0) (__smtx_typeof x1)))
  | (SmtTerm.Apply (SmtTerm.DtTester s d i) x1) => (__smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) SmtType.Bool) (__smtx_typeof x1))
  | (SmtTerm.Apply f x1) => (__smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x1))
  | (SmtTerm.Var s T) => (__smtx_typeof_guard_wf T T)
  | (SmtTerm.UConst s T) => (__smtx_typeof_guard_wf T T)
  | x1 => SmtType.None




def native_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (native_unpack_seq vs)
  | (SmtSeq.empty _) => []


def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))


def __smtx_ssm_char_values_of_string (s : native_String) : List SmtValue :=
  s.toList.map SmtValue.Char

def __smtx_ssm_char_of_value : SmtValue -> Char
  | (SmtValue.Char c) => c
  | _ => Char.ofNat 0

def __smtx_ssm_string_of_char_values (xs : List SmtValue) : native_String :=
  String.ofList (xs.map __smtx_ssm_char_of_value)

def native_unpack_string (x : SmtSeq) : native_String :=
  (__smtx_ssm_string_of_char_values (native_unpack_seq x))

def native_pack_string (s : native_String) : SmtSeq :=
  (native_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s))

  
def __smtx_value_eqb (v1 : SmtValue) (v2 : SmtValue) : native_Bool :=
  match __smtx_model_eval_eq v1 v2 with
  | (SmtValue.Boolean b) => b
  | _ => false


def native_seq_prefix_eq : List SmtValue -> List SmtValue -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | v1 :: vs1, v2 :: vs2 => (__smtx_value_eqb v1 v2) && (native_seq_prefix_eq vs1 vs2)


def native_seq_len : List SmtValue -> native_Int
  | x => Int.ofNat x.length

def native_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y
  
def native_seq_extract (xs : List SmtValue) (i : native_Int) (n : native_Int) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take


def native_seq_indexof_rec (xs pat : List SmtValue) (i fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if native_seq_prefix_eq pat xs then
        Int.ofNat i
      else
        match xs with
        | [] => -1
        | _ :: ys => (native_seq_indexof_rec ys pat (i + 1) fuel)


def native_seq_indexof (xs pat : List SmtValue) (i : native_Int) : native_Int :=
  if i < 0 then
    -1
  else
    let start := Int.toNat i
    let patLen := pat.length
    let xsLen := xs.length
    if h : start + patLen <= xsLen then
      (native_seq_indexof_rec (xs.drop start) pat start (xsLen - (start + patLen) + 1))
    else
      -1


def native_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  match pat with
  | [] => repl ++ xs
  | _ =>
      let idx := native_seq_indexof xs pat 0
      if idx < 0 then
        xs
      else
        let n := Int.toNat idx
        (xs.take n) ++ repl ++ (xs.drop (n + pat.length))


def native_seq_replace_all_aux (fuel : Nat) (pat repl : List SmtValue) :
    List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := native_seq_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                (xs.take n) ++ repl ++
                  (native_seq_replace_all_aux fuel pat repl (xs.drop (n + pat.length)))


def native_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  (native_seq_replace_all_aux (xs.length + 1) pat repl xs)


def native_seq_update (xs : List SmtValue) (i : native_Int) (ys : List SmtValue) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ ys ++ (xs.drop (idx + 1))
    
def native_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse
  
def native_seq_contains (xs pat : List SmtValue) : native_Bool :=
  (0 <= (native_seq_indexof xs pat 0))

end

end

noncomputable def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.Seq (native_pack_string s))
  | (SmtTerm.Binary w n) => (SmtValue.Binary w n)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.not) x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) x1) x2) => (__smtx_model_eval_or (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) x1) x2) => (__smtx_model_eval_imp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.xor) x1) x2) => (__smtx_model_eval_xor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.plus) x1) x2) => (__smtx_model_eval_plus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.neg) x1) x2) => (__smtx_model_eval__ (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mult) x1) x2) => (__smtx_model_eval_mult (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.lt) x1) x2) => (__smtx_model_eval_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.leq) x1) x2) => (__smtx_model_eval_leq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.gt) x1) x2) => (__smtx_model_eval_gt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.geq) x1) x2) => (__smtx_model_eval_geq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_real) x1) => (__smtx_model_eval_to_real (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_int) x1) => (__smtx_model_eval_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.is_int) x1) => (__smtx_model_eval_is_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.abs) x1) => (__smtx_model_eval_abs (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.uneg) x1) => (__smtx_model_eval_uneg (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div) x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0)) (__smtx_model_eval_apply (__smtx_model_lookup M native_div_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int)) _v1) (__smtx_model_eval_div_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod) x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0)) (__smtx_model_eval_apply (__smtx_model_lookup M native_mod_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int)) _v1) (__smtx_model_eval_mod_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult) x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (SmtValue.Numeral 0)
    let _v2 := (__smtx_model_eval M x1)
    let _v3 := (SmtValue.Numeral 1)
    (__smtx_model_eval_ite (__smtx_model_eval_geq _v0 _v1) (__smtx_model_eval_multmult_total _v2 _v0) (__smtx_model_eval_ite (__smtx_model_eval_eq _v2 _v1) (__smtx_model_eval_apply (__smtx_model_lookup M native_div_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int)) _v3) (__smtx_model_eval_div_total _v3 (__smtx_model_eval_multmult_total _v2 (__smtx_model_eval__ _v1 _v0)))))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.divisible) x1) x2) => (__smtx_model_eval_divisible (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_pow2) x1) => (__smtx_model_eval_int_pow2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_log2) x1) => (__smtx_model_eval_int_log2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div_total) x1) x2) => (__smtx_model_eval_div_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod_total) x1) x2) => (__smtx_model_eval_mod_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult_total) x1) x2) => (__smtx_model_eval_multmult_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.select) x1) x2) => (__smtx_model_eval_select (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.store) x1) x2) x3) => (__smtx_model_eval_store (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.concat) x1) x2) => (__smtx_model_eval_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.extract) x1) x2) x3) => (__smtx_model_eval_extract (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.repeat) x1) x2) => (__smtx_model_eval_repeat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnot) x1) => (__smtx_model_eval_bvnot (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvand) x1) x2) => (__smtx_model_eval_bvand (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvor) x1) x2) => (__smtx_model_eval_bvor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnand) x1) x2) => (__smtx_model_eval_bvnand (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnor) x1) x2) => (__smtx_model_eval_bvnor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxor) x1) x2) => (__smtx_model_eval_bvxor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxnor) x1) x2) => (__smtx_model_eval_bvxnor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvcomp) x1) x2) => (__smtx_model_eval_bvcomp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvneg) x1) => (__smtx_model_eval_bvneg (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvadd) x1) x2) => (__smtx_model_eval_bvadd (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvmul) x1) x2) => (__smtx_model_eval_bvmul (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvudiv) x1) x2) => (__smtx_model_eval_bvudiv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvurem) x1) x2) => (__smtx_model_eval_bvurem (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsub) x1) x2) => (__smtx_model_eval_bvsub (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdiv) x1) x2) => (__smtx_model_eval_bvsdiv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsrem) x1) x2) => (__smtx_model_eval_bvsrem (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmod) x1) x2) => (__smtx_model_eval_bvsmod (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvult) x1) x2) => (__smtx_model_eval_bvult (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvule) x1) x2) => (__smtx_model_eval_bvule (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvugt) x1) x2) => (__smtx_model_eval_bvugt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuge) x1) x2) => (__smtx_model_eval_bvuge (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvslt) x1) x2) => (__smtx_model_eval_bvslt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsle) x1) x2) => (__smtx_model_eval_bvsle (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsgt) x1) x2) => (__smtx_model_eval_bvsgt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsge) x1) x2) => (__smtx_model_eval_bvsge (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvshl) x1) x2) => (__smtx_model_eval_bvshl (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvlshr) x1) x2) => (__smtx_model_eval_bvlshr (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvashr) x1) x2) => (__smtx_model_eval_bvashr (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.zero_extend) x1) x2) => (__smtx_model_eval_zero_extend (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.sign_extend) x1) x2) => (__smtx_model_eval_sign_extend (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.rotate_left) x1) x2) => (__smtx_model_eval_rotate_left (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.rotate_right) x1) x2) => (__smtx_model_eval_rotate_right (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuaddo) x1) x2) => (__smtx_model_eval_bvuaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnego) x1) => (__smtx_model_eval_bvnego (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsaddo) x1) x2) => (__smtx_model_eval_bvsaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvumulo) x1) x2) => (__smtx_model_eval_bvumulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmulo) x1) x2) => (__smtx_model_eval_bvsmulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvusubo) x1) x2) => (__smtx_model_eval_bvusubo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvssubo) x1) x2) => (__smtx_model_eval_bvssubo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdivo) x1) x2) => (__smtx_model_eval_bvsdivo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.seq_empty x1) => (SmtValue.Seq (SmtSeq.empty x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_len) x1) => (__smtx_model_eval_str_len (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_concat) x1) x2) => (__smtx_model_eval_str_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_substr) x1) x2) x3) => (__smtx_model_eval_str_substr (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_contains) x1) x2) => (__smtx_model_eval_str_contains (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace) x1) x2) x3) => (__smtx_model_eval_str_replace (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_indexof) x1) x2) x3) => (__smtx_model_eval_str_indexof (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_at) x1) x2) => (__smtx_model_eval_str_at (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_prefixof) x1) x2) => (__smtx_model_eval_str_prefixof (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_suffixof) x1) x2) => (__smtx_model_eval_str_suffixof (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_rev) x1) => (__smtx_model_eval_str_rev (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_update) x1) x2) x3) => (__smtx_model_eval_str_update (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_lower) x1) => (__smtx_model_eval_str_to_lower (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_upper) x1) => (__smtx_model_eval_str_to_upper (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_code) x1) => (__smtx_model_eval_str_to_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_from_code) x1) => (__smtx_model_eval_str_from_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_is_digit) x1) => (__smtx_model_eval_str_is_digit (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_int) x1) => (__smtx_model_eval_str_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_from_int) x1) => (__smtx_model_eval_str_from_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_lt) x1) x2) => (__smtx_model_eval_str_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_leq) x1) x2) => (__smtx_model_eval_str_leq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_all) x1) x2) x3) => (__smtx_model_eval_str_replace_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_re) x1) x2) x3) => (__smtx_model_eval_str_replace_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_replace_re_all) x1) x2) x3) => (__smtx_model_eval_str_replace_re_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_indexof_re) x1) x2) x3) => (__smtx_model_eval_str_indexof_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.TheoryOp SmtTheoryOp.re_allchar) => (SmtValue.RegLan native_re_allchar)
  | (SmtTerm.TheoryOp SmtTheoryOp.re_none) => (SmtValue.RegLan native_re_none)
  | (SmtTerm.TheoryOp SmtTheoryOp.re_all) => (SmtValue.RegLan native_re_all)
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_to_re) x1) => (__smtx_model_eval_str_to_re (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_mult) x1) => (__smtx_model_eval_re_mult (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_plus) x1) => (__smtx_model_eval_re_plus (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_exp) x1) x2) => (__smtx_model_eval_re_exp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_opt) x1) => (__smtx_model_eval_re_opt (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_comp) x1) => (__smtx_model_eval_re_comp (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_range) x1) x2) => (__smtx_model_eval_re_range (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_concat) x1) x2) => (__smtx_model_eval_re_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_inter) x1) x2) => (__smtx_model_eval_re_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_union) x1) x2) => (__smtx_model_eval_re_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_diff) x1) x2) => (__smtx_model_eval_re_diff (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.re_loop) x1) x2) x3) => (__smtx_model_eval_re_loop (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.str_in_re) x1) x2) => (__smtx_model_eval_str_in_re (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.seq_unit) x1) => 
    let _v0 := (__smtx_model_eval M x1)
    (SmtValue.Seq (SmtSeq.cons _v0 (SmtSeq.empty (__smtx_typeof_value _v0))))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.seq_nth) x1) x2) => (__smtx_seq_nth M (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.set_empty x1) => (SmtValue.Set (SmtMap.default x1 (SmtValue.Boolean false)))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_singleton) x1) => (__smtx_model_eval_set_singleton (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_union) x1) x2) => (__smtx_model_eval_set_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_inter) x1) x2) => (__smtx_model_eval_set_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_minus) x1) x2) => (__smtx_model_eval_set_minus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_member) x1) x2) => (__smtx_model_eval_set_member (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_subset) x1) x2) => (__smtx_model_eval_set_subset (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv) x1) x2) => 
    let _v0 := (__smtx_model_eval M x2)
    let _v1 := (__smtx_model_eval M x1)
    (__smtx_model_eval_ite (__smtx_model_eval_eq _v0 (SmtValue.Rational (native_mk_rational 0 1))) (__smtx_model_eval_apply (__smtx_model_lookup M native_qdiv_by_zero_id (SmtType.FunType SmtType.Real SmtType.Real)) _v1) (__smtx_model_eval_qdiv_total _v1 _v0))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv_total) x1) x2) => (__smtx_model_eval_qdiv_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_to_bv) x1) x2) => (__smtx_model_eval_int_to_bv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.ubv_to_int) x1) => (__smtx_model_eval_ubv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.sbv_to_int) x1) => (__smtx_model_eval_sbv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.ite x1 x2 x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.eq x1 x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.exists s T x1) => (native_eval_texists M s T x1)
  | (SmtTerm.forall s T x1) => (native_eval_tforall M s T x1)
  | (SmtTerm.choice_nth s T x1 i) => (native_eval_tchoice_nth M s T x1 i)
  | (SmtTerm.DtCons s d i) => (SmtValue.DtCons s d i)
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

def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

def model_total_typed (M : SmtModel) : Prop :=
  (∀ s T, type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (∀ s T, ¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, model_total_typed M /\ (smt_interprets M t true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, model_total_typed M -> ¬ (smt_interprets M t true))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end Smtm
