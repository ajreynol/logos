import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String
abbrev smt_lit_RegLan := String --FIXME

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

-- SMT Beyond Eunoia

def smt_lit_streq : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | x, y => decide (x = y)

def smt_lit_int_log2 : smt_lit_Int -> smt_lit_Int
  | _ => 0 -- FIXME

def smt_lit_str_lt : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_from_int : smt_lit_Int -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_int : smt_lit_String -> smt_lit_Int
  | _ => 0 -- FIXME
def smt_lit_str_to_upper : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_lower : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_update : smt_lit_String -> smt_lit_Int -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_rev : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_replace : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_all : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_contains : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_to_re : smt_lit_String -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_mult : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_plus : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_comp : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_concat : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_inter : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_diff : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_union : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_range : smt_lit_String -> smt_lit_String -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_str_in_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_indexof_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Int -> smt_lit_Int
  | _, _, _ => 0 -- FIXME
def smt_lit_str_replace_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_re_all : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_re_allchar : smt_lit_RegLan := "" --FIXME
def smt_lit_re_none : smt_lit_RegLan := "" --FIXME
def smt_lit_re_all : smt_lit_RegLan := "" --FIXME

-- Partial semantics

def smt_lit_qdiv_by_zero_id : smt_lit_Int := -1
def smt_lit_div_by_zero_id : smt_lit_Int := -2
def smt_lit_mod_by_zero_id : smt_lit_Int := -3
def smt_lit_wrong_apply_sel_id : smt_lit_Int := -4

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
  | USort : smt_lit_Int -> SmtType
  | Array : SmtType -> SmtType -> SmtType
  | Set : SmtType -> SmtType

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : smt_lit_Bool -> SmtTerm
  | Numeral : smt_lit_Int -> SmtTerm
  | Rational : smt_lit_Rat -> SmtTerm
  | String : smt_lit_String -> SmtTerm
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : smt_lit_String -> SmtType -> SmtTerm
  | ite : SmtTerm
  | eq : SmtTerm
  | exists : smt_lit_String -> SmtType -> SmtTerm
  | forall : smt_lit_String -> SmtType -> SmtTerm
  | lambda : smt_lit_String -> SmtType -> SmtTerm
  | choice : smt_lit_String -> SmtType -> SmtTerm
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtTerm
  | DtSel : smt_lit_String -> SmtDatatype -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | DtTester : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtTerm
  | DtUpdater : smt_lit_String -> SmtDatatype -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Const : SmtValue -> SmtType -> SmtTerm
  | UConst : smt_lit_Int -> SmtType -> SmtTerm
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
  | _at_bvsize : SmtTerm
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
  | _at_bv : SmtTerm
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
  | set_is_empty : SmtTerm
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
  | String : smt_lit_String -> SmtValue
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtValue
  | Map : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | RegLan : smt_lit_RegLan -> SmtValue
  | Lambda : smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtValue
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

/-
SMT-LIB model
-/
abbrev SmtModel := Int -- FIXME

def __smtx_model_lookup : SmtModel -> smt_lit_Int -> SmtType -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME


/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)
/- Used for ordering values -/
def __smtx_value_hash : SmtValue -> smt_lit_Int
  | _ => 0 -- FIXME
  
/- exists -/
def smt_lit_tforall : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- forall -/
def smt_lit_texists : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- choice -/
def smt_lit_tchoice : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME

/- Definition of SMT-LIB model semantics -/

mutual

partial def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


partial def __vsm_apply_arg_nth : SmtValue -> smt_lit_Int -> SmtValue
  | (SmtValue.Apply f a), n => (smt_lit_ite (smt_lit_zeq n 0) a (__vsm_apply_arg_nth f (smt_lit_zplus n (smt_lit_zneg 1))))
  | a, n => SmtValue.NotValue


partial def __smtx_msm_get_default : SmtMap -> SmtValue
  | (SmtMap.cons j e m) => (__smtx_msm_get_default m)
  | (SmtMap.default T e) => e


partial def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (smt_lit_ite (smt_lit_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


partial def __smtx_msm_update : SmtMap -> SmtValue -> SmtValue -> SmtMap
  | (SmtMap.cons j e1 m), i, e2 => (smt_lit_ite (smt_lit_veq j i) (SmtMap.cons i e2 m) (smt_lit_ite (smt_lit_zleq (__smtx_value_hash j) (__smtx_value_hash i)) (SmtMap.cons i e2 (SmtMap.cons j e1 m)) (SmtMap.cons j e1 (__smtx_msm_update m i e2))))
  | (SmtMap.default T e1), i, e2 => (smt_lit_ite (smt_lit_veq e1 e2) (SmtMap.default T e1) (SmtMap.cons i e2 (SmtMap.default T e1)))


partial def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => (smt_lit_ite (smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) (__smtx_typeof_map_value m)) (__smtx_typeof_map_value m) SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


partial def __smtx_index_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => T
  | T => SmtType.None


partial def __smtx_elem_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => U
  | T => SmtType.None


partial def __smtx_mss_op_internal (isInter : smt_lit_Bool) : SmtMap -> SmtMap -> SmtMap -> SmtMap
  | (SmtMap.default T efalse), m2, acc => acc
  | (SmtMap.cons e etrue m1), m2, acc => (__smtx_mss_op_internal isInter m1 m2 (smt_lit_ite (smt_lit_iff (smt_lit_veq (__smtx_msm_lookup m2 e) (SmtValue.Boolean true)) isInter) (__smtx_msm_update acc e (SmtValue.Boolean true)) acc))


partial def __smtx_ssm_seq_nth : SmtSeq -> smt_lit_Int -> SmtValue
  | (SmtSeq.empty T), n => SmtValue.NotValue
  | (SmtSeq.cons v vs), 0 => v
  | (SmtSeq.cons v vs), n => (__smtx_ssm_seq_nth vs (smt_lit_zplus n (smt_lit_zneg 1)))


partial def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => (smt_lit_ite (smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)) (__smtx_typeof_seq_value vs) SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


partial def __smtx_dtc_concat : SmtDatatypeCons -> SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons U c1), c2 => (SmtDatatypeCons.cons U (__smtx_dtc_concat c1 c2))
  | SmtDatatypeCons.unit, c2 => c2


partial def __smtx_dtc_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons T c) => (SmtDatatypeCons.cons (smt_lit_ite (smt_lit_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T) (__smtx_dtc_substitute s d c))
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit


partial def __smtx_dt_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatype -> SmtDatatype
  | (SmtDatatype.sum c d2) => (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d2))
  | SmtDatatype.null => SmtDatatype.null


partial def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> smt_lit_Int -> SmtType
  | SmtDatatype.null, 0 => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), 0 => (SmtType.DtConsType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) 0))
  | (SmtDatatype.sum c d), n => (__smtx_typeof_dt_cons_value_rec T d (smt_lit_zplus n (smt_lit_zneg 1)))
  | d, n => SmtType.None


partial def __smtx_ret_typeof_sel : SmtDatatype -> smt_lit_Int -> smt_lit_Int -> SmtType
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), 0, 0 => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), 0, m => (__smtx_ret_typeof_sel (SmtDatatype.sum c d) 0 (smt_lit_zplus m (smt_lit_zneg 1)))
  | (SmtDatatype.sum c d), n, m => (__smtx_ret_typeof_sel d (smt_lit_zplus n (smt_lit_zneg 1)) m)
  | d, n, m => SmtType.None


partial def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtConsType T U), V => (smt_lit_ite (smt_lit_Teq T V) U SmtType.None)
  | T, U => SmtType.None


partial def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.String s) => (SmtType.Seq SmtType.Char)
  | (SmtValue.Binary w n) => (smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.DtCons s d n) => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


partial def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), t2, t3 => t2
  | (SmtValue.Boolean false), t2, t3 => t3
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_eq (t1 : SmtValue) (t2 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) (__smtx_typeof_value t2)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) SmtType.None) SmtValue.NotValue (SmtValue.Boolean (smt_lit_veq t1 t2))) SmtValue.NotValue)

partial def __smtx_map_select : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i => (smt_lit_ite (smt_lit_Teq (__smtx_index_typeof_map (__smtx_typeof_map_value m)) (__smtx_typeof_value i)) (__smtx_msm_lookup m i) SmtValue.NotValue)
  | v, i => SmtValue.NotValue


partial def __smtx_map_store : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i, e => (SmtValue.Map (__smtx_msm_update m i e))
  | v, i, e => SmtValue.NotValue


partial def __smtx_set_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal true m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


partial def __smtx_set_minus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal false m1 m2 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false))))
  | v1, v2 => SmtValue.NotValue


partial def __smtx_set_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (SmtValue.Map (__smtx_mss_op_internal false m1 (SmtMap.default (__smtx_index_typeof_map (__smtx_typeof_map_value m1)) (SmtValue.Boolean false)) m2))
  | v1, v2 => SmtValue.NotValue


partial def __smtx_seq_nth : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq s), (SmtValue.Numeral n) => (__smtx_ssm_seq_nth s n)
  | v1, v2 => SmtValue.NotValue


partial def __smtx_is_var (s1 : smt_lit_String) (T1 : SmtType) : SmtTerm -> smt_lit_Bool
  | (SmtTerm.Var s2 T2) => (smt_lit_and (smt_lit_streq s1 s2) (smt_lit_Teq T1 T2))
  | x => false


partial def __smtx_is_binder_x (s1 : smt_lit_String) (T1 : SmtType) : SmtTerm -> smt_lit_Bool
  | (SmtTerm.exists s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | (SmtTerm.forall s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | (SmtTerm.lambda s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | (SmtTerm.choice s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | x => false


partial def __smtx_substitute (s : smt_lit_String) (T : SmtType) (u : SmtTerm) : SmtTerm -> SmtTerm
  | (SmtTerm.Apply f a) => (smt_lit_ite (__smtx_is_binder_x s T f) (SmtTerm.Apply f a) (SmtTerm.Apply (__smtx_substitute s T u f) (__smtx_substitute s T u a)))
  | z => (smt_lit_ite (__smtx_is_var s T z) u z)


partial def __smtx_model_eval_dt_cons (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n) SmtType.None) SmtValue.NotValue (SmtValue.DtCons s d n))

partial def __smtx_model_eval_dt_sel (M : SmtModel) (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (m : smt_lit_Int) (v : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) (SmtType.Datatype s d)) (smt_lit_ite (smt_lit_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)) (__vsm_apply_arg_nth v m) (__smtx_map_select (__smtx_map_select (__smtx_map_select (__smtx_model_lookup M smt_lit_wrong_apply_sel_id (SmtType.Map SmtType.Int (SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel d n m))))) (SmtValue.Numeral n)) (SmtValue.Numeral m)) v)) SmtValue.NotValue)

partial def __smtx_model_eval_dt_tester (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (v1 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) (SmtType.Datatype s d)) (SmtValue.Boolean (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n))) SmtValue.NotValue)

partial def __smtx_model_eval_dt_updater (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (m : smt_lit_Int) (v1 : SmtValue) (v2 : SmtValue) : SmtValue :=
  SmtValue.NotValue

partial def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Map m), i => (__smtx_map_select (SmtValue.Map m) i)
  | v, i => SmtValue.NotValue


partial def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_or x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_plus : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zplus x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qplus x3 x4))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval__ : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg x2)))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qplus x3 (smt_lit_qneg x4)))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_mult : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zmult x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qmult x3 x4))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (smt_lit_zlt x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (smt_lit_qlt x3 x4))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_leq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Boolean (smt_lit_zleq x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Boolean (smt_lit_qleq x3 x4))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_to_real : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Rational (smt_lit_to_real x1))
  | (SmtValue.Rational x2) => (SmtValue.Rational x2)
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_to_int : SmtValue -> SmtValue
  | (SmtValue.Rational x1) => (SmtValue.Numeral (smt_lit_to_int x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_int_pow2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (smt_lit_int_pow2 x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_int_log2 : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.Numeral (smt_lit_int_log2 x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_div_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_div_total x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_mod_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_mod_total x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_multmult_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Numeral (smt_lit_zexp_total x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval__at_bvsize : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral x1)
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Binary (smt_lit_zplus x1 x3) (smt_lit_mod_total (smt_lit_binary_concat x1 x2 x3 x4) (smt_lit_int_pow2 (smt_lit_zplus x1 x3))))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_extract : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_and (smt_lit_zleq x2 x1) (smt_lit_and (smt_lit_zleq 0 x2) (smt_lit_zlt x1 x3))) (SmtValue.Binary (smt_lit_zplus (smt_lit_zplus x1 1) (smt_lit_zneg x2)) (smt_lit_mod_total (smt_lit_binary_extract x3 x4 x1 x2) (smt_lit_int_pow2 (smt_lit_zplus (smt_lit_zplus x1 1) (smt_lit_zneg x2))))) SmtValue.NotValue)
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_repeat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (smt_lit_ite (smt_lit_zleq 1 x1) (smt_lit_ite (smt_lit_zeq x1 1) (SmtValue.Binary x2 x3) (__smtx_model_eval_concat (SmtValue.Binary x2 x3) (__smtx_model_eval_repeat (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg 1))) (SmtValue.Binary x2 x3)))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvnot : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_not x1 x2) (smt_lit_int_pow2 x1)))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_bvand : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_and x1 x2 x4) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_or x1 x2 x4) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvxor : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_binary_xor x1 x2 x4) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvneg : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zneg x2) (smt_lit_int_pow2 x1)))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_bvadd : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zplus x2 x4) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvmul : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zmult x2 x4) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvudiv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_ite (smt_lit_zeq x4 0) (smt_lit_binary_max x1) (smt_lit_div_total x2 x4)) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvurem : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_ite (smt_lit_zeq x4 0) x2 (smt_lit_mod_total x2 x4)) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvugt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Boolean (smt_lit_zlt x4 x2)) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvshl : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_zmult x2 (smt_lit_int_pow2 x4)) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvlshr : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (smt_lit_ite (smt_lit_zeq x1 x3) (SmtValue.Binary x1 (smt_lit_mod_total (smt_lit_div_total x2 (smt_lit_int_pow2 x4)) (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_zero_extend : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtValue.Binary (smt_lit_zplus x1 x2) x3) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_rotate_left : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (smt_lit_ite (smt_lit_zleq 0 x1) (smt_lit_ite (smt_lit_zeq x1 0) (SmtValue.Binary x2 x3) (__smtx_model_eval_rotate_left (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg 1))) (__smtx_model_eval_concat (__smtx_model_eval_extract (SmtValue.Numeral (smt_lit_zplus (smt_lit_zplus x2 (smt_lit_zneg 1)) (smt_lit_zneg 1))) (SmtValue.Numeral 0) (SmtValue.Binary x2 x3)) (__smtx_model_eval_extract (SmtValue.Numeral (smt_lit_zplus x2 (smt_lit_zneg 1))) (SmtValue.Numeral (smt_lit_zplus x2 (smt_lit_zneg 1))) (SmtValue.Binary x2 x3))))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_rotate_right : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Binary x2 x3) => (smt_lit_ite (smt_lit_zleq 0 x1) (smt_lit_ite (smt_lit_zeq x1 0) (SmtValue.Binary x2 x3) (__smtx_model_eval_rotate_right (SmtValue.Numeral (smt_lit_zplus x1 (smt_lit_zneg 1))) (__smtx_model_eval_concat (__smtx_model_eval_extract (SmtValue.Numeral 0) (SmtValue.Numeral 0) (SmtValue.Binary x2 x3)) (__smtx_model_eval_extract (SmtValue.Numeral (smt_lit_zplus x2 (smt_lit_zneg 1))) (SmtValue.Numeral 1) (SmtValue.Binary x2 x3))))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvuaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_zleq (smt_lit_int_pow2 x1) (smt_lit_zplus x2 x4)))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvnego : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Boolean (smt_lit_zeq x2 (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_bvsaddo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_or (smt_lit_zleq (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1))) (smt_lit_zplus (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4))) (smt_lit_zlt (smt_lit_zplus (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4)) (smt_lit_zneg (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))))))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvumulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_zleq (smt_lit_int_pow2 x1) (smt_lit_zmult x2 x4)))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_bvsmulo : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2), (SmtValue.Binary x3 x4) => (SmtValue.Boolean (smt_lit_or (smt_lit_zleq (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1))) (smt_lit_zmult (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4))) (smt_lit_zlt (smt_lit_zmult (smt_lit_binary_uts x1 x2) (smt_lit_binary_uts x3 x4)) (smt_lit_zneg (smt_lit_int_pow2 (smt_lit_zplus x1 (smt_lit_zneg 1)))))))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval__at_bv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (smt_lit_ite (smt_lit_zleq 0 x2) (SmtValue.Binary x2 (smt_lit_mod_total x1 (smt_lit_int_pow2 x2))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_str_len : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.Numeral (smt_lit_str_len x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2) => (SmtValue.String (smt_lit_str_concat x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_str_substr : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.Numeral x2), (SmtValue.Numeral x3) => (SmtValue.String (smt_lit_str_substr x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_contains : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2) => (SmtValue.Boolean (smt_lit_str_contains x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_str_replace : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2), (SmtValue.String x3) => (SmtValue.String (smt_lit_str_replace x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_indexof : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (smt_lit_str_indexof x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_rev : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.String (smt_lit_str_rev x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_update : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.Numeral x2), (SmtValue.String x3) => (SmtValue.String (smt_lit_str_update x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_to_lower : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.String (smt_lit_str_to_lower x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_to_upper : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.String (smt_lit_str_to_upper x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_to_code : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.Numeral (smt_lit_str_to_code x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_from_code : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.String (smt_lit_str_from_code x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_to_int : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.Numeral (smt_lit_str_to_int x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_from_int : SmtValue -> SmtValue
  | (SmtValue.Numeral x1) => (SmtValue.String (smt_lit_str_from_int x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_str_lt : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2) => (SmtValue.Boolean (smt_lit_str_lt x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_str_replace_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2), (SmtValue.String x3) => (SmtValue.String (smt_lit_str_replace_all x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_replace_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.RegLan x2), (SmtValue.String x3) => (SmtValue.String (smt_lit_str_replace_re x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_replace_re_all : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.RegLan x2), (SmtValue.String x3) => (SmtValue.String (smt_lit_str_replace_re_all x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_indexof_re : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.RegLan x2), (SmtValue.Numeral x3) => (SmtValue.Numeral (smt_lit_str_indexof_re x1 x2 x3))
  | t1, t2, t3 => SmtValue.NotValue


partial def __smtx_model_eval_str_to_re : SmtValue -> SmtValue
  | (SmtValue.String x1) => (SmtValue.RegLan (smt_lit_str_to_re x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_re_mult : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (smt_lit_re_mult x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_re_comp : SmtValue -> SmtValue
  | (SmtValue.RegLan x1) => (SmtValue.RegLan (smt_lit_re_comp x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_re_range : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.String x2) => (SmtValue.RegLan (smt_lit_re_range x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_re_concat : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_concat x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_re_inter : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_inter x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_re_union : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_union x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_re_diff : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan x1), (SmtValue.RegLan x2) => (SmtValue.RegLan (smt_lit_re_diff x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_str_in_re : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.String x1), (SmtValue.RegLan x2) => (SmtValue.Boolean (smt_lit_str_in_re x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_qdiv_total : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (SmtValue.Rational (smt_lit_mk_rational x1 x2))
  | (SmtValue.Rational x3), (SmtValue.Rational x4) => (SmtValue.Rational (smt_lit_qdiv_total x3 x4))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_int_to_bv : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Numeral x1), (SmtValue.Numeral x2) => (smt_lit_ite (smt_lit_zleq 0 x1) (SmtValue.Binary x1 (smt_lit_mod_total x2 (smt_lit_int_pow2 x1))) SmtValue.NotValue)
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval_ubv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral x2)
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_sbv_to_int : SmtValue -> SmtValue
  | (SmtValue.Binary x1 x2) => (SmtValue.Numeral (smt_lit_binary_uts x1 x2))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.String s)
  | (SmtTerm.Binary w n) => (smt_lit_ite (smt_lit_and (smt_lit_zleq 0 w) (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))) (SmtValue.Binary w n) SmtValue.NotValue)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or x1) x2) => (__smtx_model_eval_or (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (SmtTerm.Apply SmtTerm.not x1)) x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) => (__smtx_model_eval M (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2) => (__smtx_model_eval M (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus x1) x2) => (__smtx_model_eval_plus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg x1) x2) => (__smtx_model_eval__ (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult x1) x2) => (__smtx_model_eval_mult (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt x1) x2) => (__smtx_model_eval_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq x1) x2) => (__smtx_model_eval_leq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt x2) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq x2) x1))
  | (SmtTerm.Apply SmtTerm.to_real x1) => (__smtx_model_eval_to_real (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.to_int x1) => (__smtx_model_eval_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.is_int x1) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply SmtTerm.to_real (SmtTerm.Apply SmtTerm.to_int x1))) x1))
  | (SmtTerm.Apply SmtTerm.abs x1) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt x1) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Numeral 0)) x1)) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x2) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.UConst smt_lit_div_by_zero_id (SmtType.Map SmtType.Int SmtType.Int)) x1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x2) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.UConst smt_lit_mod_by_zero_id (SmtType.Map SmtType.Int SmtType.Int)) x1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (SmtTerm.Numeral 1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total x1) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Numeral 0)) x2)))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod x2) x1)) (SmtTerm.Numeral 0)))
  | (SmtTerm.Apply SmtTerm.int_pow2 x1) => (__smtx_model_eval_int_pow2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.int_log2 x1) => (__smtx_model_eval_int_log2 (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total x1) x2) => (__smtx_model_eval_div_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total x1) x2) => (__smtx_model_eval_mod_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total x1) x2) => (__smtx_model_eval_multmult_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select x1) x2) => (__smtx_map_select (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store x1) x2) x3) => (__smtx_map_store (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply SmtTerm._at_bvsize x1) => (__smtx_model_eval__at_bvsize (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat x1) x2) => (__smtx_model_eval_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract x1) x2) x3) => (__smtx_model_eval_extract (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat x1) x2) => (__smtx_model_eval_repeat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.bvnot x1) => (__smtx_model_eval_bvnot (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand x1) x2) => (__smtx_model_eval_bvand (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor x1) x2) => (__smtx_model_eval_bvor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand x1) x2) => (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor x1) x2) => (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor x1) x2) => (__smtx_model_eval_bvxor (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor x1) x2) => (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 0)) (SmtTerm.Numeral 1))))
  | (SmtTerm.Apply SmtTerm.bvneg x1) => (__smtx_model_eval_bvneg (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd x1) x2) => (__smtx_model_eval_bvadd (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul x1) x2) => (__smtx_model_eval_bvmul (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv x1) x2) => (__smtx_model_eval_bvudiv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem x1) x2) => (__smtx_model_eval_bvurem (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd x1) (SmtTerm.Apply SmtTerm.bvneg x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv x1) x2)) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv (SmtTerm.Apply SmtTerm.bvneg x1)) x2))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv x1) (SmtTerm.Apply SmtTerm.bvneg x2)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv (SmtTerm.Apply SmtTerm.bvneg x1)) (SmtTerm.Apply SmtTerm.bvneg x2))))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem x1) x2)) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply SmtTerm.bvneg x1)) x2))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem x1) (SmtTerm.Apply SmtTerm.bvneg x2)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply SmtTerm.bvneg x1)) (SmtTerm.Apply SmtTerm.bvneg x2))))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 0)) (SmtTerm.Apply SmtTerm._at_bvsize x1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2)))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2)))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2))))) x2)) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2)))) x2)) (SmtTerm.Apply SmtTerm.bvneg (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) x1) (SmtTerm.Apply SmtTerm.bvneg x1))) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1))) x2) (SmtTerm.Apply SmtTerm.bvneg x2)))))))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x2) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge x2) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x1) x2) => (__smtx_model_eval_bvugt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt x2) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge x2) x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) x2)) (SmtTerm.Binary 1 1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt x1) x2))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl x1) x2) => (__smtx_model_eval_bvshl (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr x1) x2) => (__smtx_model_eval_bvlshr (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x1)) (SmtTerm.Numeral 1))) x1)) (SmtTerm.Binary 1 0))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr x1) x2)) (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr (SmtTerm.Apply SmtTerm.bvnot x1)) x2))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend x1) x2) => (__smtx_model_eval_zero_extend (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) (SmtTerm.Numeral 1))) x2) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat x1) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm._at_bvsize x2)) (SmtTerm.Numeral 1))) x2))) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left x1) x2) => (__smtx_model_eval_rotate_left (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right x1) x2) => (__smtx_model_eval_rotate_right (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo x1) x2) => (__smtx_model_eval_bvuaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.bvnego x1) => (__smtx_model_eval_bvnego (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo x1) x2) => (__smtx_model_eval_bvsaddo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo x1) x2) => (__smtx_model_eval_bvumulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo x1) x2) => (__smtx_model_eval_bvsmulo (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult x1) x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply SmtTerm.bvnego x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge x1) (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 0)) (SmtTerm.Apply SmtTerm._at_bvsize x1)))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo x1) (SmtTerm.Apply SmtTerm.bvneg x2))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply SmtTerm.bvnego x1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x2) (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 0)) (SmtTerm.Apply SmtTerm._at_bvsize x1))))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv x1) x2) => (__smtx_model_eval__at_bv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.seq_empty x1) => (SmtValue.Seq (SmtSeq.empty x1))
  | (SmtTerm.Apply SmtTerm.str_len x1) => (__smtx_model_eval_str_len (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat x1) x2) => (__smtx_model_eval_str_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x1) x2) x3) => (__smtx_model_eval_str_substr (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains x1) x2) => (__smtx_model_eval_str_contains (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace x1) x2) x3) => (__smtx_model_eval_str_replace (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof x1) x2) x3) => (__smtx_model_eval_str_indexof (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x1) x2) (SmtTerm.Numeral 1)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x2) (SmtTerm.Numeral 0)) (SmtTerm.Apply SmtTerm.str_len x1))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr x2) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm.str_len x2)) (SmtTerm.Apply SmtTerm.str_len x1))) (SmtTerm.Apply SmtTerm.str_len x1))))
  | (SmtTerm.Apply SmtTerm.str_rev x1) => (__smtx_model_eval_str_rev (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update x1) x2) x3) => (__smtx_model_eval_str_update (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply SmtTerm.str_to_lower x1) => (__smtx_model_eval_str_to_lower (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_to_upper x1) => (__smtx_model_eval_str_to_upper (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_to_code x1) => (__smtx_model_eval_str_to_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_from_code x1) => (__smtx_model_eval_str_from_code (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_is_digit x1) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq (SmtTerm.Numeral 48)) (SmtTerm.Apply SmtTerm.str_to_code x1))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq (SmtTerm.Apply SmtTerm.str_to_code x1)) (SmtTerm.Numeral 57))))
  | (SmtTerm.Apply SmtTerm.str_to_int x1) => (__smtx_model_eval_str_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.str_from_int x1) => (__smtx_model_eval_str_from_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt x1) x2) => (__smtx_model_eval_str_lt (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all x1) x2) x3) => (__smtx_model_eval_str_replace_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re x1) x2) x3) => (__smtx_model_eval_str_replace_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all x1) x2) x3) => (__smtx_model_eval_str_replace_re_all (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re x1) x2) x3) => (__smtx_model_eval_str_indexof_re (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | SmtTerm.re_allchar => (SmtValue.RegLan smt_lit_re_allchar)
  | SmtTerm.re_none => (SmtValue.RegLan smt_lit_re_none)
  | SmtTerm.re_all => (SmtValue.RegLan smt_lit_re_all)
  | (SmtTerm.Apply SmtTerm.str_to_re x1) => (__smtx_model_eval_str_to_re (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.re_mult x1) => (__smtx_model_eval_re_mult (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.re_plus x1) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat x1) (SmtTerm.Apply SmtTerm.re_mult x1)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp x1) x2) => (smt_lit_ite (smt_lit_veq (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) (SmtTerm.Numeral 0))) (SmtValue.Boolean true)) (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) (SmtTerm.Numeral 0))) (SmtTerm.Apply SmtTerm.str_to_re (SmtTerm.String ""))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg x1) (SmtTerm.Numeral 1))) x2)) x2))) SmtValue.NotValue)
  | (SmtTerm.Apply SmtTerm.re_opt x1) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union x1) (SmtTerm.Apply SmtTerm.str_to_re (SmtTerm.String ""))))
  | (SmtTerm.Apply SmtTerm.re_comp x1) => (__smtx_model_eval_re_comp (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range x1) x2) => (__smtx_model_eval_re_range (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat x1) x2) => (__smtx_model_eval_re_concat (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter x1) x2) => (__smtx_model_eval_re_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union x1) x2) => (__smtx_model_eval_re_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff x1) x2) => (__smtx_model_eval_re_diff (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop x1) x2) x3) => (smt_lit_ite (smt_lit_veq (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x1) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq x2) (SmtTerm.Numeral 0)))) (SmtValue.Boolean true)) (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt x1) x2)) SmtTerm.re_none) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp x1) x3)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop x1) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg x2) (SmtTerm.Numeral 1))) x3)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp x2) x3))))) SmtValue.NotValue)
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re x1) x2) => (__smtx_model_eval_str_in_re (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.seq_unit x1) => (SmtValue.Seq (SmtSeq.cons (__smtx_model_eval M x1) (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M x1)))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth x1) x2) => (__smtx_seq_nth (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.set_empty x1) => (SmtValue.Map (SmtMap.default x1 (SmtValue.Boolean false)))
  | (SmtTerm.Apply SmtTerm.set_singleton x1) => (SmtValue.Map (SmtMap.cons (__smtx_model_eval M x1) (SmtValue.Boolean true) (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M x1)) (SmtValue.Boolean false))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union x1) x2) => (__smtx_set_union (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter x1) x2) => (__smtx_set_inter (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus x1) x2) => (__smtx_set_minus (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member x1) x2) => (__smtx_map_select (__smtx_model_eval M x2) (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter x1) x2)) x1))
  | (SmtTerm.Apply SmtTerm.set_is_empty x1) => (SmtValue.Boolean (smt_lit_veq (__smtx_model_eval M x1) (SmtValue.Map (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M x1)) (SmtValue.Boolean false)))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv x1) x2) => (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x2) (SmtTerm.Rational (smt_lit_mk_rational 0 1)))) (SmtTerm.Apply (SmtTerm.UConst smt_lit_qdiv_by_zero_id (SmtType.Map SmtType.Real SmtType.Real)) x1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total x1) x2)))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total x1) x2) => (__smtx_model_eval_qdiv_total (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv x1) x2) => (__smtx_model_eval_int_to_bv (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply SmtTerm.ubv_to_int x1) => (__smtx_model_eval_ubv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply SmtTerm.sbv_to_int x1) => (__smtx_model_eval_sbv_to_int (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite x1) x2) x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit_tforall M s T x1)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit_texists M s T x1)
  | (SmtTerm.Apply (SmtTerm.lambda s T) x1) => (SmtValue.Lambda s T x1)
  | (SmtTerm.Apply (SmtTerm.choice s T) x1) => (smt_lit_tchoice M s T x1)
  | (SmtTerm.DtCons s d n) => (__smtx_model_eval_dt_cons s d n)
  | (SmtTerm.Apply (SmtTerm.DtSel s d n m) x1) => (__smtx_model_eval_dt_sel M s d n m (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s d n) x1) => (__smtx_model_eval_dt_tester s d n (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.DtUpdater s d n m) x1) x2) => (__smtx_model_eval_dt_updater s d n m (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Const v T) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) T) v SmtValue.NotValue)
  | (SmtTerm.UConst n T) => (__smtx_model_lookup M n T)
  | x1 => SmtValue.NotValue




end

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_interprets : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean true)) ->
      smt_interprets t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean false))->
      smt_interprets t false

/- FIXME inductive smt_model_well_typed : SmtModel -> Prop, based on smt axiom -/

/- ---------------------------------------------- -/

end Smtm
