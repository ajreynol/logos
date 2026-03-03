import Cpc.SmtEval

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Eo


/- Eunoia literal evaluation defined -/

abbrev eo_lit_Bool := SmtEval.smt_lit_Bool
abbrev eo_lit_Int := SmtEval.smt_lit_Int
abbrev eo_lit_Rat := SmtEval.smt_lit_Rat
abbrev eo_lit_String := SmtEval.smt_lit_String

partial def eo_lit_ite {T : Type} (c : eo_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev eo_lit_not := SmtEval.smt_lit_not
abbrev eo_lit_and := SmtEval.smt_lit_and
abbrev eo_lit_iff := SmtEval.smt_lit_iff
abbrev eo_lit_or := SmtEval.smt_lit_or
abbrev eo_lit_xor := SmtEval.smt_lit_xor
abbrev eo_lit_zplus := SmtEval.smt_lit_zplus
abbrev eo_lit_zmult := SmtEval.smt_lit_zmult
abbrev eo_lit_zneg := SmtEval.smt_lit_zneg
abbrev eo_lit_zeq := SmtEval.smt_lit_zeq
abbrev eo_lit_zleq := SmtEval.smt_lit_zleq
abbrev eo_lit_zlt := SmtEval.smt_lit_zlt
abbrev eo_lit_div := SmtEval.smt_lit_div
abbrev eo_lit_mod := SmtEval.smt_lit_mod
abbrev eo_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev eo_lit_piand := SmtEval.smt_lit_piand
abbrev eo_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev eo_lit_qplus := SmtEval.smt_lit_qplus
abbrev eo_lit_qmult := SmtEval.smt_lit_qmult
abbrev eo_lit_qneg := SmtEval.smt_lit_qneg
abbrev eo_lit_qeq := SmtEval.smt_lit_qeq
abbrev eo_lit_qleq := SmtEval.smt_lit_qleq
abbrev eo_lit_qlt := SmtEval.smt_lit_qlt
abbrev eo_lit_qdiv := SmtEval.smt_lit_qdiv
abbrev eo_lit_to_int := SmtEval.smt_lit_to_int
abbrev eo_lit_to_real := SmtEval.smt_lit_to_real
abbrev eo_lit_str_len := SmtEval.smt_lit_str_len
abbrev eo_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev eo_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev eo_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev eo_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev eo_lit_str_from_code := SmtEval.smt_lit_str_from_code

abbrev __smtx_pow2 := SmtEval.__smtx_pow2
abbrev __smtx_bit := SmtEval.__smtx_bit
abbrev __smtx_msb := SmtEval.__smtx_msb
abbrev __smtx_binary_or := SmtEval.__smtx_binary_or
abbrev __smtx_binary_xor := SmtEval.__smtx_binary_xor
abbrev __smtx_binary_not := SmtEval.__smtx_binary_not
abbrev __smtx_binary_max := SmtEval.__smtx_binary_max
abbrev __smtx_binary_uts := SmtEval.__smtx_binary_uts
abbrev __smtx_binary_concat := SmtEval.__smtx_binary_concat
abbrev __smtx_binary_extract := SmtEval.__smtx_binary_extract


/- Term definition -/

mutual

inductive Term : Type where
  | __eo_Proof : Term
  | __eo_pf : Term -> Term
  | Int : Term
  | Real : Term
  | BitVec : Term
  | Char : Term
  | Seq : Term
  | __eo_List : Term
  | __eo_List_nil : Term
  | __eo_List_cons : Term
  | Bool : Term
  | Boolean : eo_lit_Bool -> Term
  | Numeral : eo_lit_Int -> Term
  | Rational : eo_lit_Rat -> Term
  | String : eo_lit_String -> Term
  | Binary : eo_lit_Int -> eo_lit_Int -> Term
  | Type : Term
  | Stuck : Term
  | Apply : Term -> Term -> Term
  | FunType : Term
  | Var : eo_lit_String -> Term -> Term
  | DatatypeType : eo_lit_String -> Datatype -> Term
  | DatatypeTypeRef : eo_lit_String -> Term
  | DtCons : eo_lit_String -> Datatype -> eo_lit_Int -> Term
  | DtSel : eo_lit_String -> Datatype -> eo_lit_Int -> eo_lit_Int -> Term
  | USort : eo_lit_Int -> Term
  | UConst : eo_lit_Int -> Term -> Term
  | _at__at_Pair : Term
  | _at__at_pair : Term
  | _at__at_result_null : Term
  | _at__at_result_invalid : Term
  | ite : Term
  | not : Term
  | or : Term
  | and : Term
  | imp : Term
  | xor : Term
  | eq : Term
  | lambda : Term
  | distinct : Term
  | _at_purify : Term -> Term
  | plus : Term
  | neg : Term
  | mult : Term
  | lt : Term
  | leq : Term
  | gt : Term
  | geq : Term
  | to_real : Term
  | to_int : Term
  | is_int : Term
  | abs : Term
  | __eoo_neg_2 : Term
  | div : Term
  | mod : Term
  | divisible : Term
  | int_pow2 : Term
  | int_log2 : Term
  | int_ispow2 : Term
  | div_total : Term
  | mod_total : Term
  | _at_int_div_by_zero : Term
  | _at_mod_by_zero : Term
  | Array : Term
  | select : Term
  | store : Term
  | _at_array_deq_diff : Term -> Term -> Term
  | _at_bvsize : Term
  | concat : Term
  | extract : Term
  | repeat : Term
  | bvnot : Term
  | bvand : Term
  | bvor : Term
  | bvnand : Term
  | bvnor : Term
  | bvxor : Term
  | bvxnor : Term
  | bvcomp : Term
  | bvneg : Term
  | bvadd : Term
  | bvmul : Term
  | bvudiv : Term
  | bvurem : Term
  | bvsub : Term
  | bvsdiv : Term
  | bvsrem : Term
  | bvsmod : Term
  | bvult : Term
  | bvule : Term
  | bvugt : Term
  | bvuge : Term
  | bvslt : Term
  | bvsle : Term
  | bvsgt : Term
  | bvsge : Term
  | bvshl : Term
  | bvlshr : Term
  | bvashr : Term
  | zero_extend : Term
  | sign_extend : Term
  | rotate_left : Term
  | rotate_right : Term
  | bvite : Term
  | bvuaddo : Term
  | bvnego : Term
  | bvsaddo : Term
  | bvumulo : Term
  | bvsmulo : Term
  | bvusubo : Term
  | bvssubo : Term
  | bvsdivo : Term
  | bvultbv : Term
  | bvsltbv : Term
  | bvredand : Term
  | bvredor : Term
  | _at_bit : Term
  | _at_from_bools : Term
  | _at_bv : Term
  | RegLan : Term
  | seq_empty : Term -> Term
  | str_len : Term
  | str_concat : Term
  | str_substr : Term
  | str_contains : Term
  | str_replace : Term
  | str_indexof : Term
  | str_at : Term
  | str_prefixof : Term
  | str_suffixof : Term
  | str_rev : Term
  | str_update : Term
  | str_to_lower : Term
  | str_to_upper : Term
  | str_to_code : Term
  | str_from_code : Term
  | str_is_digit : Term
  | str_to_int : Term
  | str_from_int : Term
  | str_lt : Term
  | str_leq : Term
  | str_replace_all : Term
  | str_replace_re : Term
  | str_replace_re_all : Term
  | str_indexof_re : Term
  | re_allchar : Term
  | re_none : Term
  | re_all : Term
  | str_to_re : Term
  | re_mult : Term
  | re_plus : Term
  | re_exp : Term
  | re_opt : Term
  | re_comp : Term
  | re_range : Term
  | re_concat : Term
  | re_inter : Term
  | re_union : Term
  | re_diff : Term
  | re_loop : Term
  | str_in_re : Term
  | seq_unit : Term
  | seq_nth : Term
  | _at_re_unfold_pos_component : Term
  | _at_strings_deq_diff : Term
  | _at_strings_stoi_result : Term
  | _at_strings_stoi_non_digit : Term
  | _at_strings_itos_result : Term
  | _at_strings_num_occur : Term
  | _at_strings_num_occur_re : Term
  | _at_strings_occur_index : Term
  | _at_strings_occur_index_re : Term
  | _at_strings_replace_all_result : Term -> Term
  | _at_witness_string_length : Term
  | is : Term
  | update : Term
  | UnitTuple : Term
  | Tuple : Term
  | tuple_unit : Term
  | tuple : Term
  | tuple_select : Term
  | tuple_update : Term
  | Set : Term
  | set_empty : Term -> Term
  | set_singleton : Term
  | set_union : Term
  | set_inter : Term
  | set_minus : Term
  | set_member : Term
  | set_subset : Term
  | set_choose : Term
  | set_is_empty : Term
  | set_is_singleton : Term
  | set_insert : Term
  | _at_sets_deq_diff : Term -> Term -> Term
  | qdiv : Term
  | qdiv_total : Term
  | _at_div_by_zero : Term
  | _at__at_Monomial : Term
  | _at__at_mon : Term
  | _at__at_Polynomial : Term
  | _at__at_poly_zero : Term
  | _at__at_poly : Term
  | forall : Term
  | exists : Term
  | _at_quantifiers_skolemize : Term -> Term -> Term
  | int_to_bv : Term
  | ubv_to_int : Term
  | sbv_to_int : Term
  | _at__at_aci_sorted : Term
  | _at_const : Term -> Term -> Term

deriving Repr, DecidableEq, Inhabited

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

/- Term equality -/
def eo_lit_teq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)
  
/- Used for defining hash -/
def __smtx_hash : Term -> eo_lit_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof

/- Definition of Eunoia signature -/

mutual

partial def __eo_proven : Proof -> Term
  | (Proof.pf F) => F
  | _ => Term.Stuck


partial def __eo_Numeral : Term := Term.Int
partial def __eo_Rational : Term := Term.Real
partial def __eo_Binary : Term := (Term.Apply Term.BitVec (Term.Numeral 1))
partial def __eo_String : Term := (Term.Apply Term.Seq Term.Char)
partial def __eo_prepend_if : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean true), f, x, res => (Term.Apply (Term.Apply f x) res)
  | (Term.Boolean false), f, x, res => res
  | _, _, _, _ => Term.Stuck


partial def __eo_mk_fun_type : Term -> Term -> Term
  | T1, T2 => (Term.Apply (Term.Apply Term.FunType T1) T2)


partial def __eo_mk_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, x2 => (Term.Apply x1 x2)


partial def __eo_empty_binary : Term := (Term.Binary 0 0)
partial def __eo_binary_mod_w (w : eo_lit_Int) (n : eo_lit_Int) : Term :=
  (Term.Binary w (eo_lit_mod n (__smtx_pow2 w)))

partial def __eo_mk_binary (w : eo_lit_Int) (n : eo_lit_Int) : Term :=
  (eo_lit_ite (eo_lit_zleq 0 w) (Term.Binary w (eo_lit_mod n (__smtx_pow2 w))) Term.Stuck)

partial def __eo_is_ok : Term -> Term
  | x => (Term.Boolean (eo_lit_not (eo_lit_teq x Term.Stuck)))


partial def __eo_ite : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 (Term.Boolean true)) x2 (eo_lit_ite (eo_lit_teq x1 (Term.Boolean false)) x3 Term.Stuck))


partial def __eo_requires : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 x2) (eo_lit_ite (eo_lit_not (eo_lit_teq x1 Term.Stuck)) x3 Term.Stuck) Term.Stuck)


partial def __eo_not : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Boolean b) => (Term.Boolean (eo_lit_not b))
  | (Term.Binary w n) => (Term.Binary w (eo_lit_mod (__smtx_binary_not w n) (__smtx_pow2 w)))
  | _ => Term.Stuck


partial def __eo_and : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean b1), (Term.Boolean b2) => (Term.Boolean (eo_lit_and b1 b2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (eo_lit_ite (eo_lit_zeq w1 0) 0 (eo_lit_piand w1 n1 n2)) (__smtx_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_or : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean b1), (Term.Boolean b2) => (Term.Boolean (eo_lit_or b1 b2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (__smtx_binary_or w1 n1 n2) (__smtx_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_xor : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean b1), (Term.Boolean b2) => (Term.Boolean (eo_lit_xor b1 b2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (__smtx_binary_or w1 n1 n2) (__smtx_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_add : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral n1), (Term.Numeral n2) => (Term.Numeral (eo_lit_zplus n1 n2))
  | (Term.Rational r1), (Term.Rational r2) => (Term.Rational (eo_lit_qplus r1 r2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (eo_lit_zplus n1 n2) (__smtx_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_mul : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral n1), (Term.Numeral n2) => (Term.Numeral (eo_lit_zmult n1 n2))
  | (Term.Rational r1), (Term.Rational r2) => (Term.Rational (eo_lit_qmult r1 r2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (eo_lit_zmult n1 n2) (__smtx_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_qdiv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral n1), (Term.Numeral n2) => (eo_lit_ite (eo_lit_zeq 0 n2) Term.Stuck (Term.Rational (eo_lit_qdiv (eo_lit_to_real n1) (eo_lit_to_real n2))))
  | (Term.Rational r1), (Term.Rational r2) => (eo_lit_ite (eo_lit_qeq (eo_lit_mk_rational 0 1) r2) Term.Stuck (Term.Rational (eo_lit_qdiv r1 r2)))
  | _, _ => Term.Stuck


partial def __eo_zdiv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral n1), (Term.Numeral n2) => (eo_lit_ite (eo_lit_zeq 0 n2) Term.Stuck (Term.Numeral (eo_lit_div n1 n2)))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (eo_lit_ite (eo_lit_zeq 0 n2) (Term.Binary w1 (__smtx_binary_max w1)) (Term.Binary w1 (eo_lit_mod (eo_lit_div n1 n2) (__smtx_pow2 w1)))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_zmod : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral n1), (Term.Numeral n2) => (eo_lit_ite (eo_lit_zeq 0 n2) Term.Stuck (Term.Numeral (eo_lit_mod n1 n2)))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (eo_lit_ite (eo_lit_zeq 0 n2) (Term.Binary w1 n1) (Term.Binary w1 (eo_lit_mod (eo_lit_mod n1 n2) (__smtx_pow2 w1)))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_is_neg : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n1) => (Term.Boolean (eo_lit_zlt n1 0))
  | (Term.Rational r1) => (Term.Boolean (eo_lit_qlt r1 (eo_lit_mk_rational 0 1)))
  | _ => Term.Stuck


partial def __eo_neg : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n1) => (Term.Numeral (eo_lit_zneg n1))
  | (Term.Rational r1) => (Term.Rational (eo_lit_qneg r1))
  | (Term.Binary w n1) => (Term.Binary w (eo_lit_mod (eo_lit_zneg n1) (__smtx_pow2 w)))
  | _ => Term.Stuck


partial def __eo_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.String s1) => (Term.Numeral (eo_lit_str_len s1))
  | (Term.Binary w n1) => (Term.Numeral w)
  | _ => Term.Stuck


partial def __eo_concat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.String s1), (Term.String s2) => (Term.String (eo_lit_str_concat s1 s2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (__eo_mk_binary (eo_lit_zplus w1 w2) (__smtx_binary_concat w1 n1 w2 n2))
  | _, _ => Term.Stuck


partial def __eo_extract : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.String s1), (Term.Numeral n2), (Term.Numeral n3) => (Term.String (eo_lit_str_substr s1 n2 (eo_lit_zplus (eo_lit_zplus n3 (eo_lit_zneg n2)) 1)))
  | (Term.Binary w n1), (Term.Numeral n2), (Term.Numeral n3) => (eo_lit_ite (eo_lit_or (eo_lit_zlt n2 0) (eo_lit_zlt (eo_lit_zplus n3 (eo_lit_zneg n2)) 0)) (Term.Binary 0 0) (__eo_mk_binary (eo_lit_zplus (eo_lit_zplus n3 (eo_lit_zneg n2)) 1) (__smtx_binary_extract w n1 n2 n3)))
  | _, _, _ => Term.Stuck


partial def __eo_find : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.String s1), (Term.String s2) => (Term.Numeral (eo_lit_str_indexof s1 s2 0))
  | _, _ => Term.Stuck


partial def __eo_to_z : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n1) => (Term.Numeral n1)
  | (Term.Rational r1) => (Term.Numeral (eo_lit_to_int r1))
  | (Term.String s1) => (eo_lit_ite (eo_lit_zeq 1 (eo_lit_str_len s1)) (Term.Numeral (eo_lit_str_to_code s1)) Term.Stuck)
  | (Term.Binary w n1) => (Term.Numeral n1)
  | _ => Term.Stuck


partial def __eo_to_q : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n1) => (Term.Rational (eo_lit_to_real n1))
  | (Term.Rational r1) => (Term.Rational r1)
  | _ => Term.Stuck


partial def __eo_to_bin : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral w), (Term.Numeral n1) => (eo_lit_ite (eo_lit_zleq w 4294967296) (__eo_mk_binary w n1) Term.Stuck)
  | (Term.Numeral w), (Term.Binary w1 n1) => (eo_lit_ite (eo_lit_zleq w 4294967296) (__eo_mk_binary w n1) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_to_str : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n1) => (eo_lit_ite (eo_lit_and (eo_lit_zleq 0 n1) (eo_lit_zlt n1 196608)) (Term.String (eo_lit_str_from_code n1)) Term.Stuck)
  | (Term.String s1) => (Term.String s1)
  | _ => Term.Stuck


partial def __eo_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean (eo_lit_teq s t))


partial def __eo_is_eq : Term -> Term -> Term
  | t, s => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_and (eo_lit_not (eo_lit_teq s Term.Stuck)) (eo_lit_teq s t))))


partial def __eo_is_bool_internal : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Boolean b) => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __eo_is_bool : Term -> Term
  | t => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_teq (__eo_is_bool_internal t) (Term.Boolean true))))


partial def __eo_is_z_internal : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral n) => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __eo_is_z : Term -> Term
  | t => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_teq (__eo_is_z_internal t) (Term.Boolean true))))


partial def __eo_is_q_internal : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Rational r) => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __eo_is_q : Term -> Term
  | t => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_teq (__eo_is_q_internal t) (Term.Boolean true))))


partial def __eo_is_bin_internal : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Binary w n) => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __eo_is_bin : Term -> Term
  | t => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_teq (__eo_is_bin_internal t) (Term.Boolean true))))


partial def __eo_is_str_internal : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.String s) => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __eo_is_str : Term -> Term
  | t => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq t Term.Stuck)) (eo_lit_teq (__eo_is_str_internal t) (Term.Boolean true))))


partial def __eo_hash : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (Term.Numeral (__smtx_hash t))


partial def __eo_gt : Term -> Term -> Term
  | x, y => (__eo_is_neg (__eo_add (__eo_neg x) y))


partial def __eo_cmp : Term -> Term -> Term
  | a, b => (__eo_is_neg (__eo_add (__eo_hash b) (__eo_neg (__eo_hash a))))


partial def __eo_var : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.String s), T => (eo_lit_ite (eo_lit_teq (__eo_typeof T) Term.Type) (eo_lit_ite (eo_lit_not (eo_lit_teq (__eo_typeof T) Term.Stuck)) (Term.Var s T) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_nameof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Var s T) => (Term.String s)
  | _ => Term.Stuck


partial def __eo_is_var : Term -> Term
  | x => (Term.Boolean (eo_lit_and (eo_lit_not (eo_lit_teq (__eo_var (__eo_nameof x) (__eo_typeof x)) Term.Stuck)) (eo_lit_and (eo_lit_not (eo_lit_teq x Term.Stuck)) (eo_lit_teq x (__eo_var (__eo_nameof x) (__eo_typeof x))))))


partial def __eo_dtc_substitute (s : eo_lit_String) (d : Datatype) : DatatypeCons -> DatatypeCons
  | (DatatypeCons.cons T c) => (DatatypeCons.cons (eo_lit_ite (eo_lit_teq T (Term.DatatypeTypeRef s)) (Term.DatatypeType s d) T) (__eo_dtc_substitute s d c))
  | DatatypeCons.unit => DatatypeCons.unit


partial def __eo_dt_substitute (s : eo_lit_String) (d : Datatype) : Datatype -> Datatype
  | (Datatype.sum c d2) => (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d2))
  | Datatype.null => Datatype.null


partial def __eo_typeof_dt_cons_rec : Term -> Datatype -> eo_lit_Int -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | T, (Datatype.sum DatatypeCons.unit d), 0 => T
  | T, (Datatype.sum (DatatypeCons.cons U c) d), 0 => (Term.Apply (Term.Apply Term.FunType U) (__eo_typeof_dt_cons_rec T (Datatype.sum c d) 0))
  | T, (Datatype.sum c d), n => (__eo_typeof_dt_cons_rec T d (eo_lit_zplus n (eo_lit_zneg 1)))
  | _, _, _ => Term.Stuck


partial def __eo_typeof_dt_sel_return : Datatype -> eo_lit_Int -> eo_lit_Int -> Term
  | (Datatype.sum (DatatypeCons.cons T c) d), 0, 0 => T
  | (Datatype.sum (DatatypeCons.cons T c) d), 0, m => (__eo_typeof_dt_sel_return (Datatype.sum c d) 0 (eo_lit_zplus m (eo_lit_zneg 1)))
  | (Datatype.sum c d), n, m => (__eo_typeof_dt_sel_return d (eo_lit_zplus n (eo_lit_zneg 1)) m)
  | _, _, _ => Term.Stuck


partial def __eo_typeof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Boolean b) => Term.Bool
  | (Term.Numeral n) => (__eo_lit_type_Numeral (Term.Numeral n))
  | (Term.Rational r) => (__eo_lit_type_Rational (Term.Rational r))
  | (Term.String s) => (__eo_lit_type_String (Term.String s))
  | (Term.Binary w n) => (__eo_lit_type_Binary (Term.Binary w n))
  | (Term.Var s T) => T
  | (Term.DatatypeType s d) => Term.Type
  | (Term.DtCons s d n) => (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dt_substitute s d d) n)
  | (Term.DtSel s d n m) => (Term.Apply (Term.Apply Term.FunType (Term.DatatypeType s d)) (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) n m))
  | (Term.USort n) => Term.Type
  | (Term.UConst n T) => T
  | t => (__eo_typeof_main t)


partial def __eo_datatype_constructors_rec (s : eo_lit_String) (d : Datatype) : Datatype -> eo_lit_Int -> Term
  | (Datatype.sum c d2), ci => (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s d ci)) (__eo_datatype_constructors_rec s d d2 (eo_lit_zplus ci 1)))
  | d2, ci => Term.__eo_List_nil


partial def __eo_dt_constructors : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.DatatypeType s d) => (__eo_datatype_constructors_rec s d d 0)
  | T => (__eo_dt_constructors_main T)


partial def __eo_datatype_cons_selectors_rec (s : eo_lit_String) (d : Datatype) (n : eo_lit_Int) : Datatype -> eo_lit_Int -> eo_lit_Int -> Term
  | (Datatype.sum DatatypeCons.unit d2), 0, ai => Term.__eo_List_nil
  | (Datatype.sum (DatatypeCons.cons U c) d2), 0, ai => (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtSel s d n ai)) (__eo_datatype_cons_selectors_rec s d n d2 0 (eo_lit_zplus ai 1)))
  | (Datatype.sum c d2), ci, ai => (__eo_datatype_cons_selectors_rec s d n d2 (eo_lit_zplus ci (eo_lit_zneg 1)) ai)
  | _, _, _ => Term.Stuck


partial def __eo_dt_selectors : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.DtCons s d n) => (__eo_datatype_cons_selectors_rec s d n d n 0)
  | t => (__eo_dt_selectors_main t)


partial def __eo_is_list_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, nil, (Term.Apply (Term.Apply g x) y) => (__eo_ite (__eo_eq f g) (__eo_is_list_rec f nil y) (Term.Boolean false))
  | f, nil, z => (__eo_eq nil z)


partial def __eo_is_list : Term -> Term -> Term
  | f, x => (__eo_is_list_rec f (__eo_nil f (__eo_typeof x)) x)


partial def __eo_cons : Term -> Term -> Term -> Term
  | f, e, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (Term.Apply (Term.Apply f e) a))


partial def __eo_get_elements_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y) => (__eo_mk_apply (Term.Apply Term.__eo_List_cons x) (__eo_get_elements_rec y))
  | nil => Term.__eo_List_nil


partial def __eo_get_elements : Term -> Term -> Term
  | f, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_get_elements_rec a))


partial def __eo_list_len_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y) => (__eo_add (Term.Numeral 1) (__eo_list_len_rec y))
  | nil => (Term.Numeral 0)


partial def __eo_list_len : Term -> Term -> Term
  | f, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_len_rec a))


partial def __eo_list_concat_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z => (__eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec y z))
  | nil, z => z


partial def __eo_list_concat : Term -> Term -> Term -> Term
  | f, a, b => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_list_concat_rec a b)))


partial def __eo_list_nth_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), (Term.Numeral 0) => x
  | (Term.Apply (Term.Apply f x) y), n => (__eo_list_nth_rec y (__eo_add n (Term.Numeral (-1 : eo_lit_Int))))
  | _, _ => Term.Stuck


partial def __eo_list_nth : Term -> Term -> Term -> Term
  | f, a, n => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_nth_rec a n))


partial def __eo_list_find_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z, n => (__eo_ite (__eo_eq x z) n (__eo_list_find_rec y z (__eo_add n (Term.Numeral 1))))
  | nil, z, n => (Term.Numeral (-1 : eo_lit_Int))


partial def __eo_list_find : Term -> Term -> Term -> Term
  | f, a, e => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_find_rec a e (Term.Numeral 0)))


partial def __eo_list_rev_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), acc => (__eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc))
  | nil, acc => acc


partial def __eo_list_rev : Term -> Term -> Term
  | f, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_rev_rec a (__eo_nil f (__eo_typeof a))))


partial def __eo_list_erase_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z => (__eo_ite (__eo_eq x z) y (__eo_mk_apply (Term.Apply f x) (__eo_list_erase_rec y z)))
  | nil, z => nil


partial def __eo_list_erase : Term -> Term -> Term -> Term
  | f, a, e => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_erase_rec a e))


partial def __eo_list_erase_all_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z => (__eo_prepend_if (__eo_not (__eo_eq z x)) f x (__eo_list_erase_all_rec y z))
  | nil, z => nil


partial def __eo_list_erase_all : Term -> Term -> Term -> Term
  | f, a, e => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_erase_all_rec a e))


partial def __eo_list_setof_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y) => (__eo_mk_apply (Term.Apply f x) (__eo_list_setof_rec (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof y)) y) (Term.Boolean true) (__eo_list_erase_all_rec y x))))
  | nil => nil


partial def __eo_list_setof : Term -> Term -> Term
  | f, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_setof_rec a))


partial def __eo_list_minclude_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | y, z, (Term.Boolean false) => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) y), z, (Term.Boolean true) => (__eo_list_minclude_rec y (__eo_requires (__eo_is_list_rec Term.__eo_List_cons (__eo_nil Term.__eo_List_cons (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x)) (__eo_not (__eo_eq (__eo_requires (__eo_is_list_rec Term.__eo_List_cons (__eo_nil Term.__eo_List_cons (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x)) z)))
  | Term.__eo_List_nil, z, (Term.Boolean true) => (Term.Boolean true)
  | _, _, _ => Term.Stuck


partial def __eo_list_minclude : Term -> Term -> Term -> Term
  | f, a, b => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_list_minclude_rec (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_get_elements_rec a)) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_get_elements_rec b)) (Term.Boolean true))))


partial def __eo_list_meq : Term -> Term -> Term -> Term
  | f, a, b => (__eo_and (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_list_minclude_rec (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_get_elements_rec a)) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_get_elements_rec b)) (Term.Boolean true)))) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_minclude_rec (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_get_elements_rec b)) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_get_elements_rec a)) (Term.Boolean true)))))


partial def __eo_list_diff_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z => (__eo_prepend_if (__eo_eq (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x)) z) f x (__eo_list_diff_rec y (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x))))
  | nil, z => nil


partial def __eo_list_diff : Term -> Term -> Term -> Term
  | f, a, b => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_list_diff_rec a b)))


partial def __eo_list_inter_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y), z => (__eo_prepend_if (__eo_not (__eo_eq (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x)) z)) f x (__eo_list_inter_rec y (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof z)) z) (Term.Boolean true) (__eo_list_erase_rec z x))))
  | nil, z => nil


partial def __eo_list_inter : Term -> Term -> Term -> Term
  | f, a, b => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof b)) b) (Term.Boolean true) (__eo_list_inter_rec a b)))


partial def __eo_list_singleton_elim_2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | nil, (Term.Apply (Term.Apply f x) y) => (__eo_ite (__eo_eq y nil) x (Term.Apply (Term.Apply f x) y))
  | nil, z => z


partial def __eo_list_singleton_elim : Term -> Term -> Term
  | f, a => (__eo_requires (__eo_is_list_rec f (__eo_nil f (__eo_typeof a)) a) (Term.Boolean true) (__eo_list_singleton_elim_2 (__eo_nil f (__eo_typeof a)) a))


partial def __pair_first : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_pair t) s) => t
  | _ => Term.Stuck


partial def __pair_second : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_pair t) s) => s
  | _ => Term.Stuck


partial def __evaluate_internal : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply (Term.Apply Term.__eo_List_cons tev) Term.__eo_List_nil) => tev
  | _, _ => Term.Stuck


partial def __get_arg_list_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f x), acc => (__get_arg_list_rec f (__eo_cons Term.__eo_List_cons x acc))
  | y, acc => acc


partial def __is_app : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply g x) => (__is_app f g)
  | f, x => (__eo_eq f x)


partial def __is_var_list : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) => (__eo_ite (__eo_is_var x) (__is_var_list xs) (Term.Boolean false))
  | Term.__eo_List_nil => (Term.Boolean true)
  | _ => Term.Stuck


partial def __eo_l_1___result_combine : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | b1, b2 => Term._at__at_result_invalid


partial def __result_combine : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | b1, Term._at__at_result_null => b1
  | b1, __eo_lv_b1_2 => (__eo_ite (__eo_eq b1 __eo_lv_b1_2) b1 (__eo_l_1___result_combine b1 __eo_lv_b1_2))


partial def __eo_l_1___assoc_nil_has_type_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, nil, W => (Term.Boolean true)


partial def __assoc_nil_has_type_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2), W => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_requires (__eo_typeof x1) W (__assoc_nil_has_type_rec f x2 W)) (__eo_l_1___assoc_nil_has_type_rec f (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) W))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___assoc_nil_has_type_rec __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __assoc_nil_same_type : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) => (__eo_requires (__eo_eq f __eo_lv_f_2) (Term.Boolean true) (__assoc_nil_has_type_rec f x2 (__eo_typeof x1)))
  | _, _ => Term.Stuck


partial def __get_lambda_type : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs), B => (Term.Apply (Term.Apply Term.FunType (__eo_typeof x)) (__get_lambda_type xs B))
  | Term.__eo_List_nil, B => B
  | _, _ => Term.Stuck


partial def __eo_prog_scope : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | F, (Proof.pf G) => (Term.Apply (Term.Apply Term.imp F) G)
  | _, _ => Term.Stuck


partial def __eo_l_1___extract_antec_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.imp F1) F2), C => (__eo_cons Term.and F1 (__extract_antec_rec F2 C))
  | _, _ => Term.Stuck


partial def __extract_antec_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | C, __eo_lv_C_2 => (__eo_ite (__eo_eq C __eo_lv_C_2) (Term.Boolean true) (__eo_l_1___extract_antec_rec C __eo_lv_C_2))


partial def __eo_l_1___extract_antec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | F, C => (__extract_antec_rec F C)


partial def __extract_antec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.imp F) C), __eo_lv_C_2 => (__eo_ite (__eo_eq C __eo_lv_C_2) F (__eo_l_1___extract_antec (Term.Apply (Term.Apply Term.imp F) C) __eo_lv_C_2))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___extract_antec __eo_dv_1 __eo_dv_2)


partial def __run_process_scope : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | F, (Term.Boolean false) => (__eo_mk_apply Term.not (__extract_antec F (Term.Boolean false)))
  | F, C => (__eo_mk_apply (__eo_mk_apply Term.imp (__extract_antec F C)) C)


partial def __eo_prog_process_scope : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | C, (Proof.pf F) => (__run_process_scope F C)
  | _, _ => Term.Stuck


partial def __eo_prog_ite_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite b) t1) t2) => (Term.Apply (Term.Apply (Term.Apply Term.ite b) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite b) t1) t2)) t1)) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite b) t1) t2)) t2))
  | _ => Term.Stuck


partial def __arith_typeunion : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Int, Term.Int => Term.Int
  | Term.Real, Term.Real => Term.Real
  | Term.Real, Term.Int => Term.Real
  | Term.Int, Term.Real => Term.Real
  | _, _ => Term.Stuck


partial def __is_arith_type : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term.Int => (Term.Boolean true)
  | Term.Real => (Term.Boolean true)
  | _ => Term.Stuck


partial def __eo_l_1___assoc_nil_nth_type : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2), n => (__eo_requires (__eo_eq f __eo_lv_f_2) (Term.Boolean true) (__assoc_nil_nth_type f x2 (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))))
  | _, _, _ => Term.Stuck


partial def __assoc_nil_nth_type : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2), (Term.Numeral 0) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_typeof x1) (__eo_l_1___assoc_nil_nth_type f (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) (Term.Numeral 0)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___assoc_nil_nth_type __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_1___assoc_nil_nth : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2), n => (__eo_requires (__eo_eq f __eo_lv_f_2) (Term.Boolean true) (__assoc_nil_nth f x2 (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))))
  | _, _, _ => Term.Stuck


partial def __assoc_nil_nth : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2), (Term.Numeral 0) => (__eo_ite (__eo_eq f __eo_lv_f_2) x1 (__eo_l_1___assoc_nil_nth f (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) (Term.Numeral 0)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___assoc_nil_nth __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_prog_split : Term -> Term
  | Term.Stuck  => Term.Stuck
  | F => (Term.Apply (Term.Apply Term.or F) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F)) (Term.Boolean false)))


partial def __to_clause : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.or F1) F2) => (Term.Apply (Term.Apply Term.or F1) F2)
  | (Term.Boolean false) => (Term.Boolean false)
  | F1 => (Term.Apply (Term.Apply Term.or F1) (Term.Boolean false))


partial def __from_clause : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.or F1) F2) => (__eo_ite (__eo_eq F2 (Term.Boolean false)) F1 (Term.Apply (Term.Apply Term.or F1) F2))
  | F1 => F1


partial def __eo_prog_resolution : Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | pol, L, (Proof.pf C1), (Proof.pf C2) => (__from_clause (__eo_list_concat Term.or (__eo_ite (__eo_eq (__eo_ite pol L (Term.Apply Term.not L)) (__to_clause C1)) (Term.Boolean false) (__eo_list_erase Term.or (__to_clause C1) (__eo_ite pol L (Term.Apply Term.not L)))) (__eo_ite (__eo_eq (__eo_ite pol (Term.Apply Term.not L) L) (__to_clause C2)) (Term.Boolean false) (__eo_list_erase Term.or (__to_clause C2) (__eo_ite pol (Term.Apply Term.not L) L)))))
  | _, _, _, _ => Term.Stuck


partial def __chain_m_resolve_rec_step : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_pair Cr) rl), Cc, pol, L => (__eo_ite (__eo_eq (__eo_ite pol (Term.Apply Term.not L) L) Cc) (__eo_mk_apply (Term.Apply Term._at__at_pair Cr) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_ite pol L (Term.Apply Term.not L))) rl)) (__eo_mk_apply (__eo_mk_apply Term._at__at_pair (__eo_list_concat Term.or (__eo_list_diff Term.or Cc (__eo_mk_apply (__eo_mk_apply Term.or (__eo_ite pol (Term.Apply Term.not L) L)) rl)) Cr)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_ite pol L (Term.Apply Term.not L))) rl)))
  | _, _, _, _ => Term.Stuck


partial def __chain_m_resolve_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean true), Term.__eo_List_nil, Term.__eo_List_nil => (Term.Apply (Term.Apply Term._at__at_pair (Term.Boolean false)) (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.and C1) Cs), (Term.Apply (Term.Apply Term.__eo_List_cons pol) pols), (Term.Apply (Term.Apply Term.__eo_List_cons L) lits) => (__chain_m_resolve_rec_step (__chain_m_resolve_rec Cs pols lits) C1 pol L)
  | _, _, _ => Term.Stuck


partial def __chain_m_resolve_final : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | C1, (Term.Apply (Term.Apply Term._at__at_pair C2) (Term.Apply (Term.Apply Term.or L) rl)) => (__eo_ite (__eo_eq C1 L) C2 (__eo_list_concat Term.or (__eo_list_diff Term.or C1 (Term.Apply (Term.Apply Term.or L) rl)) C2))
  | _, _ => Term.Stuck


partial def __chain_m_resolve : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.and C1) C2), pols, lits => (__chain_m_resolve_final C1 (__chain_m_resolve_rec C2 pols lits))
  | _, _, _ => Term.Stuck


partial def __eo_prog_chain_resolution : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | pols, lits, (Proof.pf C) => (__from_clause (__chain_m_resolve C pols lits))
  | _, _, _ => Term.Stuck


partial def __eo_prog_chain_m_resolution : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | Cr, pols, lits, (Proof.pf C) => (__eo_requires (__eo_ite (__eo_eq (__from_clause (__eo_list_setof Term.or (__chain_m_resolve C pols lits))) Cr) (Term.Boolean true) (__eo_list_minclude Term.or Cr (__eo_list_setof Term.or (__chain_m_resolve C pols lits)))) (Term.Boolean true) Cr)
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_factoring : Proof -> Term
  | (Proof.pf C) => (__from_clause (__eo_list_setof Term.or C))
  | _ => Term.Stuck


partial def __eo_prog_reordering : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | C2, (Proof.pf C1) => (__eo_requires (__eo_list_minclude Term.or C1 C2) (Term.Boolean true) C2)
  | _, _ => Term.Stuck


partial def __eo_prog_eq_resolve : Proof -> Proof -> Term
  | (Proof.pf F1), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_F1_2) F2)) => (__eo_requires (__eo_eq F1 __eo_lv_F1_2) (Term.Boolean true) F2)
  | _, _ => Term.Stuck


partial def __eo_prog_modus_ponens : Proof -> Proof -> Term
  | (Proof.pf F1), (Proof.pf (Term.Apply (Term.Apply Term.imp __eo_lv_F1_2) F2)) => (__eo_requires (__eo_eq F1 __eo_lv_F1_2) (Term.Boolean true) F2)
  | _, _ => Term.Stuck


partial def __eo_prog_not_not_elim : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply Term.not F))) => F
  | _ => Term.Stuck


partial def __eo_prog_contra : Proof -> Proof -> Term
  | (Proof.pf F), (Proof.pf (Term.Apply Term.not __eo_lv_F_2)) => (__eo_requires (__eo_eq F __eo_lv_F_2) (Term.Boolean true) (Term.Boolean false))
  | _, _ => Term.Stuck


partial def __eo_prog_and_elim : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | i, (Proof.pf Fs) => (__eo_list_nth Term.and Fs i)
  | _, _ => Term.Stuck


partial def __eo_prog_and_intro : Proof -> Term
  | (Proof.pf F) => F
  | _ => Term.Stuck


partial def __eo_prog_not_or_elim : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | i, (Proof.pf (Term.Apply Term.not Fs)) => (__eo_mk_apply Term.not (__eo_list_nth Term.or Fs i))
  | _, _ => Term.Stuck


partial def __eo_prog_implies_elim : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.imp F1) F2)) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_implies_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.imp F1) F2))) => F1
  | _ => Term.Stuck


partial def __eo_prog_not_implies_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.imp F1) F2))) => (Term.Apply Term.not F2)
  | _ => Term.Stuck


partial def __eo_prog_equiv_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq F1) F2)) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_equiv_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq F1) F2)) => (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_equiv_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq F1) F2))) => (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_equiv_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq F1) F2))) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_xor_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.xor F1) F2)) => (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_xor_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.xor F1) F2)) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_xor_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.xor F1) F2))) => (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_xor_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.xor F1) F2))) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_ite_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2)) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not C)) (Term.Apply (Term.Apply Term.or F1) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_ite_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2)) => (Term.Apply (Term.Apply Term.or C) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_ite_elim1 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2))) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not C)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_not_ite_elim2 : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2))) => (Term.Apply (Term.Apply Term.or C) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __lower_not_and : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Boolean true) => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.and l) ls) => (__eo_cons Term.or (Term.Apply Term.not l) (__lower_not_and ls))
  | _ => Term.Stuck


partial def __eo_prog_not_and : Proof -> Term
  | (Proof.pf (Term.Apply Term.not F)) => (__lower_not_and F)
  | _ => Term.Stuck


partial def __eo_prog_cnf_and_pos : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Fs, i => (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not Fs)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_list_nth Term.and Fs i)) (Term.Boolean false)))


partial def __eo_prog_cnf_and_neg : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Fs => (__eo_cons Term.or Fs (__lower_not_and Fs))


partial def __eo_prog_cnf_or_pos : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Fs => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not Fs)) Fs)


partial def __eo_prog_cnf_or_neg : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Fs, i => (__eo_mk_apply (Term.Apply Term.or Fs) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_list_nth Term.or Fs i))) (Term.Boolean false)))


partial def __eo_prog_cnf_implies_pos : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.imp F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.imp F1) F2))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_implies_neg1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.imp F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.imp F1) F2)) (Term.Apply (Term.Apply Term.or F1) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_cnf_implies_neg2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.imp F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.imp F1) F2)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_cnf_equiv_pos1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq F1) F2))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_equiv_pos2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq F1) F2))) (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_equiv_neg1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq F1) F2)) (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_equiv_neg2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq F1) F2)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_xor_pos1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.xor F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.xor F1) F2))) (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_xor_pos2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.xor F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.xor F1) F2))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_xor_neg1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.xor F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.xor F1) F2)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_xor_neg2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.xor F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.xor F1) F2)) (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_pos1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not C)) (Term.Apply (Term.Apply Term.or F1) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_pos2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2))) (Term.Apply (Term.Apply Term.or C) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_pos3 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2))) (Term.Apply (Term.Apply Term.or F1) (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_neg1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not C)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_neg2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2)) (Term.Apply (Term.Apply Term.or C) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_cnf_ite_neg3 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply (Term.Apply Term.ite C) F1) F2)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not F2)) (Term.Boolean false))))
  | _ => Term.Stuck


partial def __eo_prog_arrays_read_over_write : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j), (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_i_2) __eo_lv_j_2))) => (__eo_requires (__eo_and (__eo_eq i __eo_lv_i_2) (__eo_eq j __eo_lv_j_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)) (Term.Apply (Term.Apply Term.select a) j)))
  | _, _ => Term.Stuck


partial def __eo_prog_arrays_read_over_write_contra : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) j)) (Term.Apply (Term.Apply Term.select __eo_lv_a_2) __eo_lv_j_2)))) => (__eo_requires (__eo_and (__eo_eq a __eo_lv_a_2) (__eo_eq j __eo_lv_j_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq j) i))
  | _ => Term.Stuck


partial def __eo_prog_arrays_read_over_write_1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) __eo_lv_i_2) => (__eo_requires (__eo_eq i __eo_lv_i_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e)) i)) e))
  | _ => Term.Stuck


partial def __eo_prog_arrays_ext : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select a) (Term._at_array_deq_diff a b))) (Term.Apply (Term.Apply Term.select b) (Term._at_array_deq_diff a b))))
  | _ => Term.Stuck


partial def __arith_eval_int_log_2_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral 1) => (Term.Numeral 0)
  | x => (__eo_add (Term.Numeral 1) (__arith_eval_int_log_2_rec (__eo_zdiv x (Term.Numeral 2))))


partial def __arith_eval_int_pow_2_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Numeral 0) => (Term.Numeral 1)
  | x => (__eo_mul (Term.Numeral 2) (__arith_eval_int_pow_2_rec (__eo_add x (Term.Numeral (-1 : eo_lit_Int)))))


partial def __bv_bitwidth : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec n) => n
  | _ => Term.Stuck


partial def __eo_disamb_type_seq_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply Term.Seq T)
  | _ => Term.Stuck


partial def __seq_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq Term.Char) => (Term.String "")
  | T => (Term.seq_empty T)


partial def __eo_disamb_type_set_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => (Term.Apply Term.Set T)
  | _ => Term.Stuck


partial def __dt_get_constructors : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Tuple T1) T2) => (Term.Apply (Term.Apply Term.__eo_List_cons Term.tuple) Term.__eo_List_nil)
  | Term.UnitTuple => (Term.Apply (Term.Apply Term.__eo_List_cons Term.tuple_unit) Term.__eo_List_nil)
  | (Term.Apply DC T) => (__dt_get_constructors DC)
  | D => (__eo_dt_constructors D)


partial def __tuple_get_selectors_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.UnitTuple, n => Term.__eo_List_nil
  | (Term.Apply (Term.Apply Term.Tuple T1) T2), n => (__eo_cons Term.__eo_List_cons (Term.Apply Term.tuple_select n) (__tuple_get_selectors_rec T2 (__eo_add n (Term.Numeral 1))))
  | _, _ => Term.Stuck


partial def __dt_get_selectors : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Tuple T1) T2), Term.tuple => (__tuple_get_selectors_rec (Term.Apply (Term.Apply Term.Tuple T1) T2) (Term.Numeral 0))
  | Term.UnitTuple, Term.tuple_unit => Term.__eo_List_nil
  | D, c => (__eo_dt_selectors c)


partial def __dt_get_selectors_of_app : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, (Term.Apply f a) => (__dt_get_selectors_of_app T f)
  | T, a => (__dt_get_selectors T a)


partial def __dt_arg_list : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.tuple t1) t2) => (__eo_cons Term.__eo_List_cons t1 (__dt_arg_list t2))
  | t => (__get_arg_list_rec t Term.__eo_List_nil)


partial def __dt_eq_cons : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f a), cs => (__dt_eq_cons f cs)
  | ct, (Term.Apply f a) => (__dt_eq_cons ct f)
  | ct, cs => (__eo_requires (__eo_ite (__eo_is_eq ct Term.tuple) (Term.Boolean true) (__eo_is_ok (__eo_dt_selectors ct))) (Term.Boolean true) (__eo_ite (__eo_eq ct cs) (Term.Boolean true) (__eo_requires (__eo_ite (__eo_is_eq cs Term.tuple) (Term.Boolean true) (__eo_is_ok (__eo_dt_selectors cs))) (Term.Boolean true) (Term.Boolean false))))


partial def __tuple_nth : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.tuple s) ts), (Term.Numeral 0) => s
  | (Term.Apply (Term.Apply Term.tuple s) ts), n => (__tuple_nth ts (__eo_add n (Term.Numeral (-1 : eo_lit_Int))))
  | _, _ => Term.Stuck


partial def __some_pairwise_distinct_term : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons t) ts), (Term.Apply (Term.Apply Term.__eo_List_cons s) ss) => (__eo_ite (__eo_ite (__eo_eq t s) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons t) (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil)) (__eo_typeof t))) (Term.Boolean true) (__some_pairwise_distinct_term ts ss))
  | Term.__eo_List_nil, Term.__eo_List_nil => (Term.Boolean false)
  | _, _ => Term.Stuck


partial def __set_is_not_subset : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.set_empty (Term.Apply Term.Set T)), s => (Term.Boolean false)
  | (Term.Apply Term.set_singleton e1), (Term.set_empty (Term.Apply Term.Set T)) => (Term.Boolean true)
  | (Term.Apply Term.set_singleton e1), (Term.Apply Term.set_singleton e2) => (__eo_ite (__eo_eq e1 e2) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons e1) (Term.Apply (Term.Apply Term.__eo_List_cons e2) Term.__eo_List_nil)) (__eo_typeof e1)))
  | (Term.Apply Term.set_singleton e1), (Term.Apply (Term.Apply Term.set_union (Term.Apply Term.set_singleton e2)) ss) => (__eo_ite (__eo_ite (__eo_eq e1 e2) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons e1) (Term.Apply (Term.Apply Term.__eo_List_cons e2) Term.__eo_List_nil)) (__eo_typeof e1))) (__set_is_not_subset (Term.Apply Term.set_singleton e1) ss) (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.set_union (Term.Apply Term.set_singleton e1)) ts), s => (__eo_ite (__set_is_not_subset (Term.Apply Term.set_singleton e1) s) (Term.Boolean true) (__set_is_not_subset ts s))
  | _, _ => Term.Stuck


partial def __eo_l_1___seq_distinct_terms : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean true)


partial def __seq_distinct_terms : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.seq_unit e1), s => (__seq_distinct_terms (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e1)) (__eo_nil Term.str_concat (__eo_typeof (Term.Apply Term.seq_unit e1)))) s)
  | t, (Term.Apply Term.seq_unit e2) => (__seq_distinct_terms t (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e2)) (__eo_nil Term.str_concat (__eo_typeof (Term.Apply Term.seq_unit e2)))))
  | (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e1)) ts), (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e2)) ss) => (__eo_ite (__eo_ite (__eo_eq e1 e2) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons e1) (Term.Apply (Term.Apply Term.__eo_List_cons e2) Term.__eo_List_nil)) (__eo_typeof e1))) (Term.Boolean true) (__seq_distinct_terms ts ss))
  | t, __eo_lv_t_2 => (__eo_ite (__eo_eq t __eo_lv_t_2) (Term.Boolean false) (__eo_l_1___seq_distinct_terms t __eo_lv_t_2))


partial def __dt_distinct_terms_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f a), cs, l1, l2 => (__dt_distinct_terms_rec f cs (__eo_cons Term.__eo_List_cons a l1) l2)
  | ct, (Term.Apply f a), l1, l2 => (__dt_distinct_terms_rec ct f l1 (__eo_cons Term.__eo_List_cons a l2))
  | ct, cs, l1, l2 => (__eo_ite (__eo_eq (__eo_ite (__eo_is_eq ct Term.tuple) (Term.Boolean true) (__eo_is_ok (__eo_dt_selectors ct))) (Term.Boolean true)) (__eo_ite (__eo_eq ct cs) (__some_pairwise_distinct_term l1 l2) (__eo_eq (__eo_ite (__eo_is_eq cs Term.tuple) (Term.Boolean true) (__eo_is_ok (__eo_dt_selectors cs))) (Term.Boolean true))) (Term.Boolean false))


partial def __eo_l_1___are_distinct_terms_type : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, s, Term.Int => (__eo_and (__eo_is_z t) (__eo_is_z s))
  | t, s, Term.Real => (__eo_and (__eo_is_q t) (__eo_is_q s))
  | t, s, (Term.Apply Term.Seq Term.Char) => (__eo_and (__eo_is_str t) (__eo_is_str s))
  | t, s, (Term.Apply Term.BitVec n) => (__eo_and (__eo_is_bin t) (__eo_is_bin s))
  | t, s, Term.Bool => (__eo_and (__eo_is_bool t) (__eo_is_bool s))
  | st, ss, (Term.Apply Term.Set U) => (__eo_or (__set_is_not_subset st ss) (__set_is_not_subset ss st))
  | sst, sss, (Term.Apply Term.Seq U) => (__seq_distinct_terms sst sss)
  | t, s, T => (__dt_distinct_terms_rec t s Term.__eo_List_nil Term.__eo_List_nil)


partial def __are_distinct_terms_type : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, __eo_lv_t_2, T => (__eo_ite (__eo_eq t __eo_lv_t_2) (Term.Boolean false) (__eo_l_1___are_distinct_terms_type t __eo_lv_t_2 T))


partial def __are_distinct_terms_list_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply (Term.Apply Term.__eo_List_cons s) xs), T => (__eo_ite (__are_distinct_terms_type t s T) (__are_distinct_terms_list_rec t xs T) (Term.Boolean false))
  | t, Term.__eo_List_nil, T => (Term.Boolean true)
  | _, _, _ => Term.Stuck


partial def __are_distinct_terms_list : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List_nil, T => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.__eo_List_cons t) xs), T => (__eo_ite (__are_distinct_terms_list_rec t xs T) (__are_distinct_terms_list xs T) (Term.Boolean false))
  | _, _ => Term.Stuck


partial def __eo_prog_refl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (Term.Apply (Term.Apply Term.eq t) t)


partial def __mk_symm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t1) t2) => (Term.Apply (Term.Apply Term.eq t2) t1)
  | (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) t2)) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t2) t1))
  | _ => Term.Stuck


partial def __eo_prog_symm : Proof -> Term
  | (Proof.pf F) => (__mk_symm F)
  | _ => Term.Stuck


partial def __mk_trans : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t1, t2, (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t3) t4)) tail) => (__eo_requires t2 t3 (__mk_trans t1 t4 tail))
  | t1, t2, (Term.Boolean true) => (Term.Apply (Term.Apply Term.eq t1) t2)
  | _, _, _ => Term.Stuck


partial def __eo_prog_trans : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t1) t2)) tail)) => (__mk_trans t1 t2 tail)
  | _ => Term.Stuck


partial def __eo_l_1___mk_cong_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | f, (Term.Boolean true) => f
  | _, _ => Term.Stuck


partial def __mk_cong_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f t1), (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq __eo_lv_t1_2) t2)) tail) => (__eo_ite (__eo_eq t1 __eo_lv_t1_2) (__eo_mk_apply (__mk_cong_rhs f tail) t2) (__eo_l_1___mk_cong_rhs (Term.Apply f t1) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq __eo_lv_t1_2) t2)) tail)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___mk_cong_rhs __eo_dv_1 __eo_dv_2)


partial def __eo_prog_cong : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | t, (Proof.pf E) => (__eo_mk_apply (Term.Apply Term.eq t) (__mk_cong_rhs t (__eo_list_rev Term.and E)))
  | _, _ => Term.Stuck


partial def __eo_l_1___mk_nary_cong_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | nil, (Term.Boolean true) => nil
  | _, _ => Term.Stuck


partial def __mk_nary_cong_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f s1) t), (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) s2)) tail) => (__eo_ite (__eo_eq s1 __eo_lv_s1_2) (__eo_cons f s2 (__mk_nary_cong_rhs t tail)) (__eo_l_1___mk_nary_cong_rhs (Term.Apply (Term.Apply f s1) t) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) s2)) tail)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___mk_nary_cong_rhs __eo_dv_1 __eo_dv_2)


partial def __eo_prog_nary_cong : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | t, (Proof.pf E) => (__eo_mk_apply (Term.Apply Term.eq t) (__mk_nary_cong_rhs t E))
  | _, _ => Term.Stuck


partial def __eo_prog_pairwise_cong : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | (Term.Apply f xs), (Proof.pf E) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply f xs)) (__eo_mk_apply f (__mk_nary_cong_rhs xs E)))
  | _, _ => Term.Stuck


partial def __eo_prog_true_intro : Proof -> Term
  | (Proof.pf F) => (Term.Apply (Term.Apply Term.eq F) (Term.Boolean true))
  | _ => Term.Stuck


partial def __eo_prog_true_elim : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq F) (Term.Boolean true))) => F
  | _ => Term.Stuck


partial def __eo_prog_false_intro : Proof -> Term
  | (Proof.pf (Term.Apply Term.not F)) => (Term.Apply (Term.Apply Term.eq F) (Term.Boolean false))
  | _ => Term.Stuck


partial def __eo_prog_false_elim : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq F) (Term.Boolean false))) => (Term.Apply Term.not F)
  | _ => Term.Stuck


partial def __mk_ho_cong : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f1, f2, (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t1) t2)) tail) => (__mk_ho_cong (Term.Apply f1 t1) (Term.Apply f2 t2) tail)
  | t1, t2, (Term.Boolean true) => (Term.Apply (Term.Apply Term.eq t1) t2)
  | _, _, _ => Term.Stuck


partial def __eo_prog_ho_cong : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t1) t2)) tail)) => (__mk_ho_cong t1 t2 tail)
  | _ => Term.Stuck


partial def __mk_distinct_elim_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.__eo_List_cons y) xs), b => (__eo_cons Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) (__mk_distinct_elim_rec x xs b))
  | x, Term.__eo_List_nil, b => b
  | _, _, _ => Term.Stuck


partial def __mk_distinct_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.distinct (Term.Apply (Term.Apply Term.__eo_List_cons x) xs)) => (__mk_distinct_elim_rec x xs (__mk_distinct_elim (Term.Apply Term.distinct xs)))
  | (Term.Apply Term.distinct xs) => (Term.Boolean true)
  | _ => Term.Stuck


partial def __eo_prog_distinct_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq b1) b2) => (__eo_requires (__eo_list_singleton_elim Term.and (__mk_distinct_elim b1)) b2 (Term.Apply (Term.Apply Term.eq b1) b2))
  | _ => Term.Stuck


partial def __eo_prog_distinct_true : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean true)) => (__eo_requires (__are_distinct_terms_list xs (__assoc_nil_nth_type Term.__eo_List_cons xs (Term.Numeral 0))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean true)))
  | _ => Term.Stuck


partial def __eo_prog_distinct_false : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean false)) => (__eo_requires (__eo_eq (__eo_list_setof Term.__eo_List_cons xs) xs) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_lambda_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lambda x) t)) f) => (__eo_requires (__get_arg_list_rec t Term.__eo_List_nil) x (__eo_requires (__is_app f t) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lambda x) t)) f)))
  | _ => Term.Stuck


partial def __poly_neg : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term._at__at_Polynomial => Term._at__at_Polynomial
  | (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a) c)) p) => (__eo_cons Term._at__at_poly (__eo_mk_apply (Term.Apply Term._at__at_mon a) (__eo_neg c)) (__poly_neg p))
  | _ => Term.Stuck


partial def __poly_mod_coeffs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term._at__at_Polynomial, w => Term._at__at_Polynomial
  | (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a) c)) p), w => (__eo_ite (__eo_eq (__eo_zmod (__eo_to_z c) w) (Term.Numeral 0)) (__poly_mod_coeffs p w) (__eo_cons Term._at__at_poly (__eo_mk_apply (Term.Apply Term._at__at_mon a) (__eo_to_q (__eo_zmod (__eo_to_z c) w))) (__poly_mod_coeffs p w)))
  | _, _ => Term.Stuck


partial def __poly_add : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a1) c1)) p1), (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a2) c2)) p2) => (__eo_ite (__eo_eq a1 a2) (__eo_ite (__eo_eq (__eo_add c1 c2) (Term.Rational (eo_lit_mk_rational 0 1))) (__poly_add p1 p2) (__eo_cons Term._at__at_poly (__eo_mk_apply (Term.Apply Term._at__at_mon a1) (__eo_add c1 c2)) (__poly_add p1 p2))) (__eo_ite (__eo_cmp a2 a1) (__eo_cons Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a1) c1) (__poly_add p1 (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a2) c2)) p2))) (__eo_cons Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a2) c2) (__poly_add (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a1) c1)) p1) p2))))
  | Term._at__at_Polynomial, p => p
  | p, Term._at__at_Polynomial => p
  | _, _ => Term.Stuck


partial def __mvar_mul_mvar : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.mult a1) a2), (Term.Apply (Term.Apply Term.mult c1) c2) => (__eo_ite (__eo_cmp c1 a1) (__eo_cons Term.mult a1 (__mvar_mul_mvar a2 (Term.Apply (Term.Apply Term.mult c1) c2))) (__eo_cons Term.mult c1 (__mvar_mul_mvar (Term.Apply (Term.Apply Term.mult a1) a2) c2)))
  | (Term.Apply (Term.Apply Term.mult a1) a2), (Term.Numeral 1) => (Term.Apply (Term.Apply Term.mult a1) a2)
  | (Term.Numeral 1), (Term.Apply (Term.Apply Term.mult c1) c2) => (Term.Apply (Term.Apply Term.mult c1) c2)
  | (Term.Apply (Term.Apply Term.bvmul ba1) ba2), (Term.Apply (Term.Apply Term.bvmul bc1) bc2) => (__eo_ite (__eo_cmp bc1 ba1) (__eo_cons Term.bvmul ba1 (__mvar_mul_mvar ba2 (Term.Apply (Term.Apply Term.bvmul bc1) bc2))) (__eo_cons Term.bvmul bc1 (__mvar_mul_mvar (Term.Apply (Term.Apply Term.bvmul ba1) ba2) bc2)))
  | (Term.Apply (Term.Apply Term.bvmul ba1) ba2), bc1 => (__eo_requires (__eo_to_z bc1) (Term.Numeral 1) (Term.Apply (Term.Apply Term.bvmul ba1) ba2))
  | ba1, (Term.Apply (Term.Apply Term.bvmul bc1) bc2) => (__eo_requires (__eo_to_z ba1) (Term.Numeral 1) (Term.Apply (Term.Apply Term.bvmul bc1) bc2))
  | ba1, bc1 => (__eo_requires (__eo_to_z ba1) (Term.Numeral 1) (__eo_requires (__eo_to_z bc1) (Term.Numeral 1) ba1))


partial def __mon_mul_mon : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_mon a1) c1), (Term.Apply (Term.Apply Term._at__at_mon a2) c2) => (__eo_mk_apply (__eo_mk_apply Term._at__at_mon (__mvar_mul_mvar a1 a2)) (__eo_mul c1 c2))
  | _, _ => Term.Stuck


partial def __poly_mul_mon : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | m1, (Term.Apply (Term.Apply Term._at__at_poly m2) p2) => (__poly_add (__eo_mk_apply (__eo_mk_apply Term._at__at_poly (__mon_mul_mon m1 m2)) Term._at__at_Polynomial) (__poly_mul_mon m1 p2))
  | m1, Term._at__at_Polynomial => Term._at__at_Polynomial
  | _, _ => Term.Stuck


partial def __poly_mul : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_poly m) p1), p => (__poly_add (__poly_mul_mon m p) (__poly_mul p1 p))
  | Term._at__at_Polynomial, p => Term._at__at_Polynomial
  | p, Term._at__at_Polynomial => Term._at__at_Polynomial
  | _, _ => Term.Stuck


partial def __get_arith_poly_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.__eoo_neg_2 a1) => (__poly_neg (__get_arith_poly_norm a1))
  | (Term.Apply (Term.Apply Term.plus a1) a2) => (__poly_add (__get_arith_poly_norm a1) (__get_arith_poly_norm a2))
  | (Term.Apply (Term.Apply Term.neg a1) a2) => (__poly_add (__get_arith_poly_norm a1) (__poly_neg (__get_arith_poly_norm a2)))
  | (Term.Apply (Term.Apply Term.mult a1) a2) => (__poly_mul (__get_arith_poly_norm a1) (__get_arith_poly_norm a2))
  | (Term.Apply (Term.Apply Term.qdiv a1) a2) => (__eo_ite (__eo_ite (__eo_is_q (__eo_to_q a2)) (__eo_not (__eo_eq (__eo_to_q a2) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Boolean false)) (__poly_mul_mon (__eo_mk_apply (Term.Apply Term._at__at_mon (Term.Numeral 1)) (__eo_qdiv (Term.Rational (eo_lit_mk_rational 1 1)) (__eo_to_q a2))) (__get_arith_poly_norm a1)) (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.qdiv a1) a2)) (Term.Numeral 1))) (Term.Rational (eo_lit_mk_rational 1 1)))) Term._at__at_Polynomial))
  | (Term.Apply (Term.Apply Term.qdiv_total a1) a2) => (__eo_ite (__eo_ite (__eo_is_q (__eo_to_q a2)) (__eo_not (__eo_eq (__eo_to_q a2) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Boolean false)) (__poly_mul_mon (__eo_mk_apply (Term.Apply Term._at__at_mon (Term.Numeral 1)) (__eo_qdiv (Term.Rational (eo_lit_mk_rational 1 1)) (__eo_to_q a2))) (__get_arith_poly_norm a1)) (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.qdiv a1) a2)) (Term.Numeral 1))) (Term.Rational (eo_lit_mk_rational 1 1)))) Term._at__at_Polynomial))
  | (Term.Apply Term.to_real a1) => (__get_arith_poly_norm a1)
  | a => (__eo_ite (__eo_is_q (__eo_to_q a)) (__eo_ite (__eo_is_eq (__eo_to_q a) (Term.Rational (eo_lit_mk_rational 0 1))) Term._at__at_Polynomial (__eo_mk_apply (__eo_mk_apply Term._at__at_poly (__eo_mk_apply (Term.Apply Term._at__at_mon (Term.Numeral 1)) (__eo_to_q a))) Term._at__at_Polynomial)) (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon (Term.Apply (Term.Apply Term.mult a) (Term.Numeral 1))) (Term.Rational (eo_lit_mk_rational 1 1)))) Term._at__at_Polynomial))


partial def __get_bv_poly_norm_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.bvneg b1) => (__poly_neg (__get_bv_poly_norm_rec b1))
  | (Term.Apply (Term.Apply Term.bvadd b1) b2) => (__poly_add (__get_bv_poly_norm_rec b1) (__get_bv_poly_norm_rec b2))
  | (Term.Apply (Term.Apply Term.bvsub b1) b2) => (__poly_add (__get_bv_poly_norm_rec b1) (__poly_neg (__get_bv_poly_norm_rec b2)))
  | (Term.Apply (Term.Apply Term.bvmul b1) b2) => (__poly_mul (__get_bv_poly_norm_rec b1) (__get_bv_poly_norm_rec b2))
  | b => (__eo_ite (__eo_is_bin b) (__eo_ite (__eo_is_eq (__eo_to_z b) (Term.Numeral 0)) Term._at__at_Polynomial (__eo_mk_apply (__eo_mk_apply Term._at__at_poly (__eo_mk_apply (__eo_mk_apply Term._at__at_mon (__eo_to_bin (__bv_bitwidth (__eo_typeof b)) (Term.Numeral 1))) (__eo_to_q (__eo_to_z b)))) Term._at__at_Polynomial)) (__eo_mk_apply (__eo_mk_apply Term._at__at_poly (__eo_mk_apply (__eo_mk_apply Term._at__at_mon (__eo_mk_apply (Term.Apply Term.bvmul b) (__eo_nil Term.bvmul (__eo_typeof b)))) (Term.Rational (eo_lit_mk_rational 1 1)))) Term._at__at_Polynomial))


partial def __arith_poly_to_term_rec : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term._at__at_Polynomial => (Term.Rational (eo_lit_mk_rational 0 1))
  | (Term.Apply (Term.Apply Term._at__at_poly (Term.Apply (Term.Apply Term._at__at_mon a) c)) p) => (__eo_mk_apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult c) (Term.Apply (Term.Apply Term.mult a) (Term.Numeral 1)))) (__eo_mk_apply (__eo_mk_apply Term.plus (__arith_poly_to_term_rec p)) (Term.Numeral 0)))
  | _ => Term.Stuck


partial def __arith_rel_sum : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | Term.lt, Term.lt, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.lt, Term.eq, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.lt, Term.leq, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.leq, Term.lt, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.leq, Term.eq, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | Term.leq, Term.leq, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | Term.eq, Term.lt, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.eq, Term.eq, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | Term.eq, Term.leq, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | _, _, _, _ => Term.Stuck


partial def __mk_arith_sum_ub : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean true), acc => acc
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply r1 a1) b1)) tail), (Term.Apply (Term.Apply r2 a2) b2) => (__mk_arith_sum_ub tail (__arith_rel_sum r1 r2 (Term.Apply (Term.Apply Term.plus a1) a2) (Term.Apply (Term.Apply Term.plus b1) b2)))
  | _, _ => Term.Stuck


partial def __eo_prog_arith_sum_ub : Proof -> Term
  | (Proof.pf F) => (__mk_arith_sum_ub (__eo_list_rev Term.and F) (Term.Apply (Term.Apply Term.eq (Term.Numeral 0)) (Term.Numeral 0)))
  | _ => Term.Stuck


partial def __mk_arith_mult_pos : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | m, (Term.Apply (Term.Apply r a) b) => (Term.Apply (Term.Apply r (Term.Apply (Term.Apply Term.mult m) (Term.Apply (Term.Apply Term.mult a) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.mult m) (Term.Apply (Term.Apply Term.mult b) (Term.Numeral 1))))
  | _, _ => Term.Stuck


partial def __eo_prog_arith_mult_pos : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | m, F => (__eo_mk_apply (__eo_mk_apply Term.imp (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.gt m) (__eo_ite (__eo_is_eq (__eo_typeof m) Term.Int) (Term.Numeral 0) (__eo_requires (__eo_typeof m) Term.Real (Term.Rational (eo_lit_mk_rational 0 1)))))) (Term.Apply (Term.Apply Term.and F) (Term.Boolean true)))) (__mk_arith_mult_pos m F))


partial def __arith_rel_inv : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.eq, a, b => (Term.Apply (Term.Apply Term.eq a) b)
  | Term.lt, a, b => (Term.Apply (Term.Apply Term.gt a) b)
  | Term.leq, a, b => (Term.Apply (Term.Apply Term.geq a) b)
  | Term.gt, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.geq, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | _, _, _ => Term.Stuck


partial def __mk_arith_mult_neg : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | m, (Term.Apply (Term.Apply r a) b) => (__arith_rel_inv r (Term.Apply (Term.Apply Term.mult m) (Term.Apply (Term.Apply Term.mult a) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.mult m) (Term.Apply (Term.Apply Term.mult b) (Term.Numeral 1))))
  | _, _ => Term.Stuck


partial def __eo_prog_arith_mult_neg : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | m, F => (__eo_mk_apply (__eo_mk_apply Term.imp (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.lt m) (__eo_ite (__eo_is_eq (__eo_typeof m) Term.Int) (Term.Numeral 0) (__eo_requires (__eo_typeof m) Term.Real (Term.Rational (eo_lit_mk_rational 0 1)))))) (Term.Apply (Term.Apply Term.and F) (Term.Boolean true)))) (__mk_arith_mult_neg m F))


partial def __arith_rel_trichotomy : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | Term.eq, Term.lt, a, b => (Term.Apply (Term.Apply Term.gt a) b)
  | Term.eq, Term.gt, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.gt, Term.eq, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | Term.lt, Term.eq, a, b => (Term.Apply (Term.Apply Term.gt a) b)
  | Term.gt, Term.lt, a, b => (Term.Apply (Term.Apply Term.eq a) b)
  | Term.lt, Term.gt, a, b => (Term.Apply (Term.Apply Term.eq a) b)
  | _, _, _, _ => Term.Stuck


partial def __arith_rel_neg : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.lt, a, b => (Term.Apply (Term.Apply Term.geq a) b)
  | Term.leq, a, b => (Term.Apply (Term.Apply Term.gt a) b)
  | Term.gt, a, b => (Term.Apply (Term.Apply Term.leq a) b)
  | Term.geq, a, b => (Term.Apply (Term.Apply Term.lt a) b)
  | _, _, _ => Term.Stuck


partial def __arith_normalize_lit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.not (Term.Apply Term.not (Term.Apply (Term.Apply r a) b))) => (Term.Apply (Term.Apply r a) b)
  | (Term.Apply Term.not (Term.Apply (Term.Apply r a) b)) => (__arith_rel_neg r a b)
  | (Term.Apply (Term.Apply r a) b) => (Term.Apply (Term.Apply r a) b)
  | _ => Term.Stuck


partial def __mk_arith_trichotomy : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply r1 a) b), (Term.Apply (Term.Apply r2 __eo_lv_a_2) __eo_lv_b_2) => (__eo_requires (__eo_and (__eo_eq a __eo_lv_a_2) (__eo_eq b __eo_lv_b_2)) (Term.Boolean true) (__arith_rel_trichotomy r1 r2 a b))
  | _, _ => Term.Stuck


partial def __eo_prog_arith_trichotomy : Proof -> Proof -> Term
  | (Proof.pf F1), (Proof.pf F2) => (__mk_arith_trichotomy (__arith_normalize_lit (Term.Apply Term.not F1)) (__arith_normalize_lit (Term.Apply Term.not F2)))
  | _, _ => Term.Stuck


partial def __greatest_int_lt : Term -> Term
  | Term.Stuck  => Term.Stuck
  | c => (__eo_ite (__eo_eq (__eo_to_q c) (__eo_to_q (__eo_to_z c))) (__eo_add (Term.Numeral (-1 : eo_lit_Int)) (__eo_to_z c)) (__eo_to_z c))


partial def __eo_prog_int_tight_ub : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.lt s) t)) => (__eo_mk_apply (Term.Apply Term.leq s) (__greatest_int_lt t))
  | _ => Term.Stuck


partial def __least_int_gt : Term -> Term
  | Term.Stuck  => Term.Stuck
  | c => (__eo_add (Term.Numeral 1) (__eo_to_z c))


partial def __eo_prog_int_tight_lb : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.gt s) t)) => (__eo_mk_apply (Term.Apply Term.geq s) (__least_int_gt t))
  | _ => Term.Stuck


partial def __eo_prog_arith_mult_tangent : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | x, y, a, b, s => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply (__eo_ite s Term.geq Term.leq) (Term.Apply (Term.Apply Term.mult x) (Term.Apply (Term.Apply Term.mult y) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult x) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult a) (Term.Apply (Term.Apply Term.mult y) (Term.Numeral 1)))) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.mult a) (Term.Apply (Term.Apply Term.mult b) (Term.Numeral 1)))))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq x) a)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply (__eo_ite s Term.leq Term.geq) y) b)) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq x) a)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply (__eo_ite s Term.geq Term.leq) y) b)) (Term.Boolean true)))) (Term.Boolean false))))


partial def __eo_l_1___strip_even_exponent : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, m => m


partial def __strip_even_exponent : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) (Term.Apply (Term.Apply Term.mult __eo_lv_t_3) m)) => (__eo_ite (__eo_and (__eo_eq t __eo_lv_t_2) (__eo_eq t __eo_lv_t_3)) (__strip_even_exponent t m) (__eo_l_1___strip_even_exponent t (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) (Term.Apply (Term.Apply Term.mult __eo_lv_t_3) m))))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___strip_even_exponent __eo_dv_1 __eo_dv_2)


partial def __eo_l_3___mk_arith_mult_sign_sgn : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | sgn, (Term.Boolean true), (Term.Numeral 1) => sgn
  | sgn, l, m => (__mk_arith_mult_sign_sgn sgn (Term.Apply (Term.Apply Term.and l) (Term.Boolean true)) m)


partial def __eo_l_2___mk_arith_mult_sign_sgn : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | sgn, (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt t) z)) F), (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) m) => (__eo_ite (__eo_eq t __eo_lv_t_2) (__eo_requires (__eo_to_z z) (Term.Numeral 0) (__mk_arith_mult_sign_sgn (__eo_not sgn) F (__strip_even_exponent t m))) (__eo_l_3___mk_arith_mult_sign_sgn sgn (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt t) z)) F) (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) m)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_3___mk_arith_mult_sign_sgn __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_1___mk_arith_mult_sign_sgn : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | sgn, (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt t) z)) F), (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) m) => (__eo_ite (__eo_eq t __eo_lv_t_2) (__eo_requires (__eo_to_z z) (Term.Numeral 0) (__mk_arith_mult_sign_sgn sgn F (__strip_even_exponent t m))) (__eo_l_2___mk_arith_mult_sign_sgn sgn (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt t) z)) F) (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) m)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_2___mk_arith_mult_sign_sgn __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __mk_arith_mult_sign_sgn : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | sgn, (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t) z))) F), (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) (Term.Apply (Term.Apply Term.mult __eo_lv_t_3) m)) => (__eo_ite (__eo_and (__eo_eq t __eo_lv_t_2) (__eo_eq t __eo_lv_t_3)) (__eo_requires (__eo_to_z z) (Term.Numeral 0) (__mk_arith_mult_sign_sgn sgn F (__strip_even_exponent t m))) (__eo_l_1___mk_arith_mult_sign_sgn sgn (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t) z))) F) (Term.Apply (Term.Apply Term.mult __eo_lv_t_2) (Term.Apply (Term.Apply Term.mult __eo_lv_t_3) m))))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___mk_arith_mult_sign_sgn __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_prog_arith_mult_sign : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | F, m => (__eo_mk_apply (Term.Apply Term.imp F) (__eo_mk_apply (__eo_mk_apply (__eo_ite (__mk_arith_mult_sign_sgn (Term.Boolean true) F m) Term.gt Term.lt) m) (__eo_ite (__eo_is_eq (__eo_typeof m) Term.Int) (Term.Numeral 0) (__eo_requires (__eo_typeof m) Term.Real (Term.Rational (eo_lit_mk_rational 0 1))))))


partial def __eo_l_2___mk_arith_mult_abs_comparison_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Boolean true), (Term.Apply (Term.Apply r a) b) => (Term.Apply (Term.Apply r (Term.Apply Term.abs a)) (Term.Apply Term.abs b))
  | _, _ => Term.Stuck


partial def __eo_l_1___mk_arith_mult_abs_comparison_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_t_2) z))) (Term.Boolean true)))) B), (Term.Apply (Term.Apply Term.gt a) b) => (__eo_ite (__eo_eq t __eo_lv_t_2) (__eo_requires (__eo_to_z z) (Term.Numeral 0) (__mk_arith_mult_abs_comparison_rec B (__eo_mk_apply (__eo_mk_apply Term.gt (__eo_list_concat Term.mult a (Term.Apply (Term.Apply Term.mult t) (Term.Numeral 1)))) (__eo_list_concat Term.mult b (Term.Apply (Term.Apply Term.mult u) (Term.Numeral 1)))))) (__eo_l_2___mk_arith_mult_abs_comparison_rec (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_t_2) z))) (Term.Boolean true)))) B) (Term.Apply (Term.Apply Term.gt a) b)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_2___mk_arith_mult_abs_comparison_rec __eo_dv_1 __eo_dv_2)


partial def __mk_arith_mult_abs_comparison_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply r (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) B), (Term.Apply (Term.Apply __eo_lv_r_2 a) b) => (__eo_ite (__eo_eq r __eo_lv_r_2) (__mk_arith_mult_abs_comparison_rec B (__eo_mk_apply (__eo_mk_apply r (__eo_list_concat Term.mult a (Term.Apply (Term.Apply Term.mult t) (Term.Numeral 1)))) (__eo_list_concat Term.mult b (Term.Apply (Term.Apply Term.mult u) (Term.Numeral 1))))) (__eo_l_1___mk_arith_mult_abs_comparison_rec (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply r (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) B) (Term.Apply (Term.Apply __eo_lv_r_2 a) b)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___mk_arith_mult_abs_comparison_rec __eo_dv_1 __eo_dv_2)


partial def __mk_arith_mult_abs_comparison : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) B) => (__mk_arith_mult_abs_comparison_rec B (Term.Apply (Term.Apply Term.gt (Term.Apply (Term.Apply Term.mult t) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.mult u) (Term.Numeral 1))))
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.abs t)) (Term.Apply Term.abs u))) B) => (__mk_arith_mult_abs_comparison_rec B (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mult t) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.mult u) (Term.Numeral 1))))
  | _ => Term.Stuck


partial def __eo_prog_arith_mult_abs_comparison : Proof -> Term
  | (Proof.pf F) => (__mk_arith_mult_abs_comparison F)
  | _ => Term.Stuck


partial def __arith_reduction_pred : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.is_int u) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.is_int u)) (Term.Apply (Term.Apply Term.eq u) (Term.Apply Term.to_real (Term._at_purify (Term.Apply Term.to_int u)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Rational (eo_lit_mk_rational 0 1))) (Term.Apply (Term.Apply Term.neg u) (Term.Apply Term.to_real (Term._at_purify (Term.Apply Term.to_int u)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.neg u) (Term.Apply Term.to_real (Term._at_purify (Term.Apply Term.to_int u))))) (Term.Rational (eo_lit_mk_rational 1 1)))) (Term.Boolean true)))) (Term.Boolean true)))
  | (Term.Apply Term.to_int u) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_int u)) (Term._at_purify (Term.Apply Term.to_int u)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Rational (eo_lit_mk_rational 0 1))) (Term.Apply (Term.Apply Term.neg u) (Term.Apply Term.to_real (Term._at_purify (Term.Apply Term.to_int u)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.neg u) (Term.Apply Term.to_real (Term._at_purify (Term.Apply Term.to_int u))))) (Term.Rational (eo_lit_mk_rational 1 1)))) (Term.Boolean true)))) (Term.Boolean true)))
  | (Term.Apply (Term.Apply Term.qdiv u) v) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv u) v)) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.eq v) (__eo_ite (__eo_is_eq (__eo_typeof v) Term.Int) (Term.Numeral 0) (__eo_requires (__eo_typeof v) Term.Real (Term.Rational (eo_lit_mk_rational 0 1)))))) (__eo_mk_apply Term._at_div_by_zero (__eo_ite (__eo_eq (__eo_typeof u) Term.Int) (Term.Apply Term.to_real u) u))) (Term.Apply (Term.Apply Term.qdiv_total u) v)))
  | (Term.Apply (Term.Apply Term.div a) b) => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div a) b)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq b) (Term.Numeral 0))) (Term.Apply Term._at_int_div_by_zero a)) (Term.Apply (Term.Apply Term.div_total a) b)))
  | (Term.Apply (Term.Apply Term.mod a) b) => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod a) b)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq b) (Term.Numeral 0))) (Term.Apply Term._at_mod_by_zero a)) (Term.Apply (Term.Apply Term.mod_total a) b)))
  | (Term.Apply (Term.Apply Term.qdiv_total u) v) => (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv_total u) v)) (Term._at_purify (Term.Apply (Term.Apply Term.qdiv_total u) v)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.imp (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_ite (__eo_eq (__eo_typeof v) Term.Int) (Term.Apply Term.to_real v) v)) (Term.Rational (eo_lit_mk_rational 0 1))))) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.mult (__eo_ite (__eo_eq (__eo_typeof v) Term.Int) (Term.Apply Term.to_real v) v)) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.qdiv_total u) v))) (Term.Numeral 1)))) (__eo_ite (__eo_eq (__eo_typeof u) Term.Int) (Term.Apply Term.to_real u) u)))) (Term.Boolean true)))
  | (Term.Apply (Term.Apply Term.div_total a) b) => (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total a) b)) (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_ite (__eo_is_z b) (__eo_requires (__eo_eq b (Term.Numeral 0)) (Term.Boolean false) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.lt a) (__eo_mk_apply (Term.Apply Term.mult b) (__eo_mk_apply (__eo_mk_apply Term.mult (__eo_mk_apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_ite (__eo_is_neg b) (Term.Numeral (-1 : eo_lit_Int)) (Term.Numeral 1))) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.gt b) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt a) (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.lt b) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt a) (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Apply (Term.Apply Term.plus (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true))))) (Term.Boolean true))))) (Term.Boolean true)))
  | (Term.Apply (Term.Apply Term.mod_total a) b) => (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total a) b)) (Term.Apply (Term.Apply Term.neg a) (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_ite (__eo_is_z b) (__eo_requires (__eo_eq b (Term.Numeral 0)) (Term.Boolean false) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.lt a) (__eo_mk_apply (Term.Apply Term.mult b) (__eo_mk_apply (__eo_mk_apply Term.mult (__eo_mk_apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_ite (__eo_is_neg b) (Term.Numeral (-1 : eo_lit_Int)) (Term.Numeral 1))) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.gt b) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt a) (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.lt b) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Numeral 1)))) a)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt a) (Term.Apply (Term.Apply Term.mult b) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.plus (Term._at_purify (Term.Apply (Term.Apply Term.div_total a) b))) (Term.Apply (Term.Apply Term.plus (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral 0)))) (Term.Numeral 1))))) (Term.Boolean true))))) (Term.Boolean true))))) (Term.Boolean true)))
  | (Term.Apply Term.abs u) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.abs u)) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.lt u) (__eo_ite (__eo_is_eq (__eo_typeof u) Term.Int) (Term.Numeral 0) (__eo_requires (__eo_typeof u) Term.Real (Term.Rational (eo_lit_mk_rational 0 1)))))) (Term.Apply Term.__eoo_neg_2 u)) u))
  | (Term.Apply Term.int_log2 u) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_log2 u)) (Term._at_purify (Term.Apply Term.int_log2 u)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.lt (Term.Numeral 0)) u)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.int_pow2 (Term._at_purify (Term.Apply Term.int_log2 u)))) u)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt u) (Term.Apply Term.int_pow2 (Term.Apply (Term.Apply Term.plus (Term._at_purify (Term.Apply Term.int_log2 u))) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))) (Term.Boolean true))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Numeral 0)) u))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply Term.int_log2 u))) (Term.Numeral 0)))) (Term.Boolean true)))) (Term.Boolean true)))
  | _ => Term.Stuck


partial def __eo_prog_arith_reduction : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (__arith_reduction_pred t)


partial def __eo_prog_arith_poly_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__get_arith_poly_norm a) (__get_arith_poly_norm b) (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __is_poly_norm_rel_consts : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.lt cx) cy) => (__eo_eq (__eo_ite (__eo_is_neg cx) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cx)) (Term.Numeral 1) (Term.Numeral 0))) (__eo_ite (__eo_is_neg cy) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cy)) (Term.Numeral 1) (Term.Numeral 0))))
  | (Term.Apply (Term.Apply Term.leq cx) cy) => (__eo_eq (__eo_ite (__eo_is_neg cx) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cx)) (Term.Numeral 1) (Term.Numeral 0))) (__eo_ite (__eo_is_neg cy) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cy)) (Term.Numeral 1) (Term.Numeral 0))))
  | (Term.Apply (Term.Apply Term.eq cx) cy) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.geq cx) cy) => (__eo_eq (__eo_ite (__eo_is_neg cx) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cx)) (Term.Numeral 1) (Term.Numeral 0))) (__eo_ite (__eo_is_neg cy) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cy)) (Term.Numeral 1) (Term.Numeral 0))))
  | (Term.Apply (Term.Apply Term.gt cx) cy) => (__eo_eq (__eo_ite (__eo_is_neg cx) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cx)) (Term.Numeral 1) (Term.Numeral 0))) (__eo_ite (__eo_is_neg cy) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_neg cy)) (Term.Numeral 1) (Term.Numeral 0))))
  | b => (Term.Boolean false)


partial def __eo_l_1___is_eq_maybe_to_real : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.to_real x), __eo_lv_x_2 => (__eo_requires (__eo_eq x __eo_lv_x_2) (Term.Boolean true) (Term.Boolean true))
  | _, _ => Term.Stuck


partial def __is_eq_maybe_to_real : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x, __eo_lv_x_2 => (__eo_ite (__eo_eq x __eo_lv_x_2) (Term.Boolean true) (__eo_l_1___is_eq_maybe_to_real x __eo_lv_x_2))


partial def __eo_prog_arith_poly_norm_rel : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply r x1) x2)) (Term.Apply (Term.Apply __eo_lv_r_2 y1) y2)), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mult cx) (Term.Apply (Term.Apply Term.mult x) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.mult cy) (Term.Apply (Term.Apply Term.mult y) (Term.Numeral 1))))) => (__eo_requires (__eo_eq r __eo_lv_r_2) (Term.Boolean true) (__eo_requires (__is_poly_norm_rel_consts (Term.Apply (Term.Apply r cx) cy)) (Term.Boolean true) (__eo_requires (__is_eq_maybe_to_real x (Term.Apply (Term.Apply Term.neg x1) x2)) (Term.Boolean true) (__eo_requires (__is_eq_maybe_to_real y (Term.Apply (Term.Apply Term.neg y1) y2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply r x1) x2)) (Term.Apply (Term.Apply r y1) y2))))))
  | _, _ => Term.Stuck


partial def __bv_unfold_repeat_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral 0), b => (Term.Binary 0 0)
  | n, b => (__eo_cons Term.concat b (__bv_unfold_repeat_rec (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) b))


partial def __bv_get_first_const_child : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f a) b) => (__eo_ite (__eo_is_bin a) a (__bv_get_first_const_child b))
  | _ => Term.Stuck


partial def __bv_bitblast_concat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools x) y), z => (__eo_cons Term._at_from_bools x (__bv_bitblast_concat y z))
  | (Term.Binary 0 0), z => z
  | _, _ => Term.Stuck


partial def __bv_bitblast_binary_app : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.and, a, b => (Term.Apply (Term.Apply Term.and a) (Term.Apply (Term.Apply Term.and b) (Term.Boolean true)))
  | Term.or, a, b => (Term.Apply (Term.Apply Term.or a) (Term.Apply (Term.Apply Term.or b) (Term.Boolean false)))
  | Term.xor, a, b => (Term.Apply (Term.Apply Term.xor a) b)
  | Term.eq, a, b => (Term.Apply (Term.Apply Term.eq a) b)
  | _, _, _ => Term.Stuck


partial def __bv_bitblast_repeat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | b, (Term.Numeral 0) => (Term.Binary 0 0)
  | b, n => (__eo_cons Term._at_from_bools b (__bv_bitblast_repeat b (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))))


partial def __bv_bitblast_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral 0), t => (Term.Binary 0 0)
  | l, (Term.Binary 0 0) => (Term.Binary 0 0)
  | l, (Term.Apply (Term.Apply Term._at_from_bools b) a) => (__eo_cons Term._at_from_bools b (__bv_bitblast_prefix (__eo_add l (Term.Numeral (-1 : eo_lit_Int))) a))
  | _, _ => Term.Stuck


partial def __bv_bitblast_head : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools b) a) => b
  | _ => Term.Stuck


partial def __bv_bitblast_tail : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools b) a) => a
  | _ => Term.Stuck


partial def __bv_bitblast_subsequence : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | l, u, (Term.Binary 0 0) => (Term.Binary 0 0)
  | (Term.Numeral 0), u, t => (__bv_bitblast_prefix (__eo_add u (Term.Numeral 1)) t)
  | l, u, (Term.Apply (Term.Apply Term._at_from_bools b) a) => (__bv_bitblast_subsequence (__eo_add l (Term.Numeral (-1 : eo_lit_Int))) (__eo_add u (Term.Numeral (-1 : eo_lit_Int))) a)
  | _, _, _ => Term.Stuck


partial def __bv_bitblast_apply_unary : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | f, (Term.Binary 0 0) => (Term.Binary 0 0)
  | f, (Term.Apply (Term.Apply Term._at_from_bools b1) a1) => (__eo_cons Term._at_from_bools (Term.Apply f b1) (__bv_bitblast_apply_unary f a1))
  | _, _ => Term.Stuck


partial def __bv_bitblast_apply_binary : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Binary 0 0), (Term.Binary 0 0) => (Term.Binary 0 0)
  | f, (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2) => (__eo_cons Term._at_from_bools (__bv_bitblast_binary_app f b1 b2) (__bv_bitblast_apply_binary f a1 a2))
  | _, _, _ => Term.Stuck


partial def __bv_bitblast_apply_ite : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | bc, (Term.Binary 0 0), (Term.Binary 0 0) => (Term.Binary 0 0)
  | bc, (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2) => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply (Term.Apply Term.ite bc) b1) b2) (__bv_bitblast_apply_ite bc a1 a2))
  | _, _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_eq_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0), (Term.Binary 0 0) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2) => (__eo_cons Term.and (Term.Apply (Term.Apply Term.eq b1) b2) (__bv_mk_bitblast_step_eq_rec a1 a2))
  | _, _ => Term.Stuck


partial def __bv_bitblast_ult_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0), (Term.Binary 0 0), res => res
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2), res => (__bv_bitblast_ult_rec a1 a2 (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq b1) b2)) (Term.Apply (Term.Apply Term.and res) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply Term.not b1)) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true)))) (Term.Boolean false))))
  | _, _, _ => Term.Stuck


partial def __bv_bitblast_ult : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2), orEqual => (__bv_bitblast_ult_rec a1 a2 (Term.Apply (Term.Apply Term.and (Term.Apply Term.not b1)) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true))))
  | _, _, _ => Term.Stuck


partial def __bv_bitblast_slt_impl : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools b1) (Term.Binary 0 0)), (Term.Apply (Term.Apply Term._at_from_bools b2) (Term.Binary 0 0)), orEqual => (__eo_ite orEqual (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq b1) b2)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not b2)) (Term.Boolean true)))) (Term.Boolean false))) (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not b2)) (Term.Boolean true))))
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2), orEqual => (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq b1) b2)) (__eo_mk_apply (__eo_mk_apply Term.and (__bv_bitblast_ult (__eo_list_rev Term._at_from_bools a1) (__eo_list_rev Term._at_from_bools a2) orEqual)) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not b2)) (Term.Boolean true)))) (Term.Boolean false)))
  | _, _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_concat : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0) => (Term.Binary 0 0)
  | (Term.Apply (Term.Apply Term.concat a1) a2) => (__bv_bitblast_concat (__bv_mk_bitblast_step_concat a2) a1)
  | _ => Term.Stuck


partial def __eo_l_1___bv_mk_bitblast_step_bitwise : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | bf, f, a2, ac => ac


partial def __bv_mk_bitblast_step_bitwise : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | bf, f, (Term.Apply (Term.Apply __eo_lv_bf_2 a1) a2), ac => (__eo_ite (__eo_eq bf __eo_lv_bf_2) (__bv_mk_bitblast_step_bitwise bf f a2 (__bv_bitblast_apply_binary f ac a1)) (__eo_l_1___bv_mk_bitblast_step_bitwise bf f (Term.Apply (Term.Apply __eo_lv_bf_2 a1) a2) ac))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3, __eo_dv_4 => (__eo_l_1___bv_mk_bitblast_step_bitwise __eo_dv_1 __eo_dv_2 __eo_dv_3 __eo_dv_4)


partial def __bv_ripple_carry_adder_2 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2), carry, res => (__bv_ripple_carry_adder_2 a1 a2 (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.xor b1) b2)) (Term.Apply (Term.Apply Term.and carry) (Term.Boolean true)))) (Term.Boolean false))) (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply Term.xor (Term.Apply (Term.Apply Term.xor b1) b2)) carry) res))
  | (Term.Binary 0 0), (Term.Binary 0 0), carry, res => (__eo_mk_apply (Term.Apply Term._at__at_pair carry) (__eo_list_rev Term._at_from_bools res))
  | _, _, _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_add : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.bvadd a1) a2), ac => (__bv_mk_bitblast_step_add a2 (__pair_second (__bv_ripple_carry_adder_2 ac a1 (Term.Boolean false) (Term.Binary 0 0))))
  | a2, ac => ac


partial def __bv_shift_add_multiplier_rec_step : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | b1, a2, (Term.Numeral 0), (Term.Binary 0 0), carry => (Term.Binary 0 0)
  | b1, (Term.Apply (Term.Apply Term._at_from_bools b2) a2), (Term.Numeral 0), (Term.Apply (Term.Apply Term._at_from_bools br) ar), carry => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply Term.xor (Term.Apply (Term.Apply Term.xor br) (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true))))) carry) (__bv_shift_add_multiplier_rec_step b1 a2 (Term.Numeral 0) ar (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and br) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.xor br) (Term.Apply (Term.Apply Term.and b1) (Term.Apply (Term.Apply Term.and b2) (Term.Boolean true))))) (Term.Apply (Term.Apply Term.and carry) (Term.Boolean true)))) (Term.Boolean false)))))
  | b1, a2, k, (Term.Apply (Term.Apply Term._at_from_bools br) ar), carry => (__eo_cons Term._at_from_bools br (__bv_shift_add_multiplier_rec_step b1 a2 (__eo_add k (Term.Numeral (-1 : eo_lit_Int))) ar carry))
  | _, _, _, _, _ => Term.Stuck


partial def __bv_shift_add_multiplier_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0), a2, k, res => res
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), a2, k, res => (__bv_shift_add_multiplier_rec a1 a2 (__eo_add k (Term.Numeral 1)) (__bv_shift_add_multiplier_rec_step b1 a2 k res (Term.Boolean false)))
  | _, _, _, _ => Term.Stuck


partial def __bv_shift_add_multiplier : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | a2, (Term.Apply (Term.Apply Term._at_from_bools b1) a1) => (__bv_shift_add_multiplier_rec a1 a2 (Term.Numeral 1) (__bv_bitblast_apply_binary Term.and (__bv_bitblast_repeat b1 (__bv_bitwidth (__eo_typeof a2))) a2))
  | _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_mul : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.bvmul a1) a2), ac => (__bv_mk_bitblast_step_mul a2 (__bv_shift_add_multiplier ac a1))
  | a2, ac => ac


partial def __eo_l_1___bv_div_mod_impl : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, a2, zero, sz => (__eo_mk_apply (__eo_mk_apply Term._at__at_pair (__bv_bitblast_apply_ite (__eo_mk_apply Term.not (__pair_first (__bv_ripple_carry_adder_2 a1 (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0)))) zero (__eo_cons Term._at_from_bools (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply Term.not (__pair_first (__bv_ripple_carry_adder_2 (__pair_second (__bv_ripple_carry_adder_2 (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))) zero (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (__eo_mk_apply Term.eq (__bv_bitblast_head a1)) (Term.Boolean true))) (Term.Boolean true)) (Term.Boolean false)) (Term.Binary 0 0))) (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0))))) (__bv_bitblast_head (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_first (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_first (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))))) (Term.Boolean true)) (__bv_bitblast_tail (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_first (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_first (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))))))) (__bv_bitblast_apply_ite (__eo_mk_apply Term.not (__pair_first (__bv_ripple_carry_adder_2 a1 (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0)))) a1 (__bv_bitblast_apply_ite (__eo_mk_apply Term.not (__pair_first (__bv_ripple_carry_adder_2 (__pair_second (__bv_ripple_carry_adder_2 (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))) zero (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (__eo_mk_apply Term.eq (__bv_bitblast_head a1)) (Term.Boolean true))) (Term.Boolean true)) (Term.Boolean false)) (Term.Binary 0 0))) (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0)))) (__pair_second (__bv_ripple_carry_adder_2 (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))) zero (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (__eo_mk_apply Term.eq (__bv_bitblast_head a1)) (Term.Boolean true))) (Term.Boolean true)) (Term.Boolean false)) (Term.Binary 0 0))) (__pair_second (__bv_ripple_carry_adder_2 (__pair_second (__bv_ripple_carry_adder_2 (__bv_bitblast_concat (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0)) (__bv_bitblast_subsequence (Term.Numeral 0) (__eo_add (__eo_add (__eo_list_len Term._at_from_bools (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__pair_second (__bv_div_mod_impl (__bv_bitblast_concat (__bv_bitblast_subsequence (Term.Numeral 1) (__eo_list_len Term._at_from_bools a1) a1) (Term.Apply (Term.Apply Term._at_from_bools (Term.Boolean false)) (Term.Binary 0 0))) a2 zero (__eo_add sz (Term.Numeral (-1 : eo_lit_Int))))))) zero (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (__eo_mk_apply Term.eq (__bv_bitblast_head a1)) (Term.Boolean true))) (Term.Boolean true)) (Term.Boolean false)) (Term.Binary 0 0))) (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0))))))


partial def __bv_div_mod_impl : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, a2, zero, (Term.Numeral 0) => (Term.Apply (Term.Apply Term._at__at_pair zero) zero)
  | zero, a2, __eo_lv_zero_2, sz => (__eo_ite (__eo_eq zero __eo_lv_zero_2) (Term.Apply (Term.Apply Term._at__at_pair zero) zero) (__eo_l_1___bv_div_mod_impl zero a2 __eo_lv_zero_2 sz))


partial def __bv_mk_bitblast_step_ite : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at_from_bools bc) (Term.Binary 0 0)), (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b2) a2) => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply Term.not bc)) (Term.Apply (Term.Apply Term.or b1) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or bc) (Term.Apply (Term.Apply Term.or b2) (Term.Boolean false)))) (Term.Boolean true))) (__bv_mk_bitblast_step_ite (Term.Apply (Term.Apply Term._at_from_bools bc) (Term.Binary 0 0)) a1 a2))
  | (Term.Apply (Term.Apply Term._at_from_bools bc) (Term.Binary 0 0)), (Term.Binary 0 0), (Term.Binary 0 0) => (Term.Binary 0 0)
  | _, _, _ => Term.Stuck


partial def __eo_l_1___bv_const_to_bitlist_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | c, i, n => (__eo_cons Term._at_from_bools (__eo_eq (__eo_extract c i i) (Term.Binary 1 1)) (__bv_const_to_bitlist_rec c (__eo_add i (Term.Numeral 1)) n))


partial def __bv_const_to_bitlist_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | c, n, __eo_lv_n_2 => (__eo_ite (__eo_eq n __eo_lv_n_2) (Term.Binary 0 0) (__eo_l_1___bv_const_to_bitlist_rec c n __eo_lv_n_2))


partial def __bv_mk_bitblast_step_shl_rec_step : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0), a1c, i, b2 => (Term.Binary 0 0)
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b1c) a1c), (Term.Numeral 0), b2 => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply (Term.Apply Term.ite b2) b1c) b1) (__bv_mk_bitblast_step_shl_rec_step a1 a1c (Term.Numeral 0) b2))
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), a1c, i, b2 => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply (Term.Apply Term.ite b2) (Term.Boolean false)) b1) (__bv_mk_bitblast_step_shl_rec_step a1 a1c (__eo_add i (Term.Numeral (-1 : eo_lit_Int))) b2))
  | _, _, _, _ => Term.Stuck


partial def __eo_l_1___bv_mk_bitblast_step_shl_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, (Term.Apply (Term.Apply Term._at_from_bools b2) a2), s, lsz => (__bv_mk_bitblast_step_shl_rec (__bv_mk_bitblast_step_shl_rec_step a1 a1 (__eo_ite (__eo_is_z s) (__eo_ite (__eo_is_neg s) (Term.Numeral 0) (__arith_eval_int_pow_2_rec s)) (Term.Apply Term.int_pow2 s)) b2) a2 (__eo_add s (Term.Numeral 1)) lsz)
  | _, _, _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_shl_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, a2, lsz, __eo_lv_lsz_2 => (__eo_ite (__eo_eq lsz __eo_lv_lsz_2) a1 (__eo_l_1___bv_mk_bitblast_step_shl_rec a1 a2 lsz __eo_lv_lsz_2))


partial def __bv_mk_bitblast_step_shr_rec_step : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Binary 0 0), a1c, i, b2, sbit => (Term.Binary 0 0)
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Apply (Term.Apply Term._at_from_bools b1c) a1c), (Term.Numeral 0), b2, sbit => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not b2)) b1) b1c) (__bv_mk_bitblast_step_shr_rec_step a1 a1c (Term.Numeral 0) b2 sbit))
  | (Term.Apply (Term.Apply Term._at_from_bools b1) a1), (Term.Binary 0 0), (Term.Numeral 0), b2, sbit => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply (Term.Apply Term.ite b2) sbit) b1) (__bv_mk_bitblast_step_shr_rec_step a1 (Term.Binary 0 0) (Term.Numeral 0) b2 sbit))
  | a1, (Term.Apply (Term.Apply Term._at_from_bools b1c) a1c), i, b2, sbit => (__bv_mk_bitblast_step_shr_rec_step a1 a1c (__eo_add i (Term.Numeral (-1 : eo_lit_Int))) b2 sbit)
  | _, _, _, _, _ => Term.Stuck


partial def __eo_l_1___bv_mk_bitblast_step_shr_rec : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, (Term.Apply (Term.Apply Term._at_from_bools b2) a2), s, lsz, sbit => (__bv_mk_bitblast_step_shr_rec (__bv_mk_bitblast_step_shr_rec_step a1 a1 (__eo_ite (__eo_is_z s) (__eo_ite (__eo_is_neg s) (Term.Numeral 0) (__arith_eval_int_pow_2_rec s)) (Term.Apply Term.int_pow2 s)) b2 sbit) a2 (__eo_add s (Term.Numeral 1)) lsz sbit)
  | _, _, _, _, _ => Term.Stuck


partial def __bv_mk_bitblast_step_shr_rec : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | a1, a2, lsz, __eo_lv_lsz_2, sbit => (__eo_ite (__eo_eq lsz __eo_lv_lsz_2) a1 (__eo_l_1___bv_mk_bitblast_step_shr_rec a1 a2 lsz __eo_lv_lsz_2 sbit))


partial def __bv_mk_bitblast_step_var_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | a, (Term.Numeral (-1 : eo_lit_Int)) => (Term.Binary 0 0)
  | a, i => (__eo_cons Term._at_from_bools (Term.Apply (Term.Apply Term._at_bit i) a) (__bv_mk_bitblast_step_var_rec a (__eo_add i (Term.Numeral (-1 : eo_lit_Int)))))


partial def __bv_mk_bitblast_step : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.bvnot a1) => (__bv_bitblast_apply_unary Term.not a1)
  | (Term.Apply (Term.Apply Term.eq a1) a2) => (__eo_list_singleton_elim Term.and (__bv_mk_bitblast_step_eq_rec a1 a2))
  | (Term.Apply (Term.Apply Term.bvult a1) a2) => (__bv_bitblast_ult a1 a2 (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.bvule a1) a2) => (__bv_bitblast_ult a1 a2 (Term.Boolean true))
  | (Term.Apply (Term.Apply Term.bvslt a1) a2) => (__bv_bitblast_slt_impl (__eo_list_rev Term._at_from_bools a1) (__eo_list_rev Term._at_from_bools a2) (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.bvsle a1) a2) => (__bv_bitblast_slt_impl (__eo_list_rev Term._at_from_bools a1) (__eo_list_rev Term._at_from_bools a2) (Term.Boolean true))
  | (Term.Apply (Term.Apply (Term.Apply Term.extract u) l) a1) => (__bv_bitblast_subsequence l u a1)
  | (Term.Apply (Term.Apply Term.concat a1) a3) => (__bv_mk_bitblast_step_concat (Term.Apply (Term.Apply Term.concat a1) a3))
  | (Term.Apply (Term.Apply Term.bvor a1) a2) => (__bv_mk_bitblast_step_bitwise Term.bvor Term.or a2 a1)
  | (Term.Apply (Term.Apply Term.bvand a1) a2) => (__bv_mk_bitblast_step_bitwise Term.bvand Term.and a2 a1)
  | (Term.Apply (Term.Apply Term.bvxor a1) a2) => (__bv_mk_bitblast_step_bitwise Term.bvxor Term.xor a2 a1)
  | (Term.Apply (Term.Apply Term.bvxnor a1) a2) => (__bv_bitblast_apply_binary Term.eq a1 a2)
  | (Term.Apply (Term.Apply Term.bvadd a1) a2) => (__bv_mk_bitblast_step_add a2 a1)
  | (Term.Apply (Term.Apply Term.bvmul a1) a2) => (__bv_mk_bitblast_step_mul a2 a1)
  | (Term.Apply (Term.Apply Term.bvudiv a1) a2) => (__bv_bitblast_apply_ite (__eo_list_singleton_elim Term.and (__bv_mk_bitblast_step_eq_rec a2 (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))))) (__bv_bitblast_repeat (Term.Boolean true) (__bv_bitwidth (__eo_typeof a1))) (__pair_first (__bv_div_mod_impl a1 a2 (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))) (__bv_bitwidth (__eo_typeof a1)))))
  | (Term.Apply (Term.Apply Term.bvurem a1) a2) => (__bv_bitblast_apply_ite (__eo_list_singleton_elim Term.and (__bv_mk_bitblast_step_eq_rec a2 (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))))) a1 (__pair_second (__bv_div_mod_impl a1 a2 (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))) (__bv_bitwidth (__eo_typeof a1)))))
  | (Term.Apply (Term.Apply Term.bvsub a1) a2) => (__pair_second (__bv_ripple_carry_adder_2 a1 (__bv_bitblast_apply_unary Term.not a2) (Term.Boolean true) (Term.Binary 0 0)))
  | (Term.Apply Term.bvneg a1) => (__pair_second (__bv_ripple_carry_adder_2 (__bv_bitblast_apply_unary Term.not a1) (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))) (Term.Boolean true) (Term.Binary 0 0)))
  | (Term.Apply (Term.Apply (Term.Apply Term.bvite ac) a1) a2) => (__bv_mk_bitblast_step_ite ac a1 a2)
  | (Term.Apply (Term.Apply Term.bvashr a1) a2) => (__bv_bitblast_apply_ite (__bv_bitblast_ult a2 (__bv_const_to_bitlist_rec (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0) (__eo_len (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))))) (Term.Boolean false)) (__bv_mk_bitblast_step_shr_rec a1 a2 (Term.Numeral 0) (__eo_ite (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a1))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a1))) (Term.Boolean false) (__eo_eq (__bv_bitwidth (__eo_typeof a1)) (__eo_ite (__eo_is_z (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (__eo_ite (__eo_is_neg (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))) (__eo_mk_apply Term.int_pow2 (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))))) (__eo_mk_apply Term.int_ispow2 (__bv_bitwidth (__eo_typeof a1)))) (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (__eo_add (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (Term.Numeral 1))) (__bv_bitblast_head (__eo_list_rev Term._at_from_bools a1))) (__bv_bitblast_repeat (__bv_bitblast_head (__eo_list_rev Term._at_from_bools a1)) (__bv_bitwidth (__eo_typeof a1))))
  | (Term.Apply (Term.Apply Term.bvlshr a1) a2) => (__bv_bitblast_apply_ite (__bv_bitblast_ult a2 (__bv_const_to_bitlist_rec (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0) (__eo_len (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))))) (Term.Boolean false)) (__bv_mk_bitblast_step_shr_rec a1 a2 (Term.Numeral 0) (__eo_ite (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a1))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a1))) (Term.Boolean false) (__eo_eq (__bv_bitwidth (__eo_typeof a1)) (__eo_ite (__eo_is_z (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (__eo_ite (__eo_is_neg (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))) (__eo_mk_apply Term.int_pow2 (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))))) (__eo_mk_apply Term.int_ispow2 (__bv_bitwidth (__eo_typeof a1)))) (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (__eo_add (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (Term.Numeral 1))) (Term.Boolean false)) (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))))
  | (Term.Apply (Term.Apply Term.bvshl a1) a2) => (__bv_bitblast_apply_ite (__bv_bitblast_ult a2 (__bv_const_to_bitlist_rec (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0) (__eo_len (__eo_to_bin (__bv_bitwidth (__eo_typeof a1)) (__bv_bitwidth (__eo_typeof a1))))) (Term.Boolean false)) (__bv_mk_bitblast_step_shl_rec a1 a2 (Term.Numeral 0) (__eo_ite (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a1))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a1))) (Term.Boolean false) (__eo_eq (__bv_bitwidth (__eo_typeof a1)) (__eo_ite (__eo_is_z (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (__eo_ite (__eo_is_neg (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))) (__eo_mk_apply Term.int_pow2 (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)))))) (__eo_mk_apply Term.int_ispow2 (__bv_bitwidth (__eo_typeof a1)))) (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (__eo_add (__eo_ite (__eo_is_neg (__eo_neg (__bv_bitwidth (__eo_typeof a1)))) (__arith_eval_int_log_2_rec (__bv_bitwidth (__eo_typeof a1))) (Term.Numeral 0)) (Term.Numeral 1)))) (__bv_bitblast_repeat (Term.Boolean false) (__bv_bitwidth (__eo_typeof a1))))
  | (Term.Apply (Term.Apply Term.bvcomp a1) a2) => (__eo_mk_apply (__eo_mk_apply Term._at_from_bools (__eo_list_singleton_elim Term.and (__bv_mk_bitblast_step_eq_rec a1 a2))) (Term.Binary 0 0))
  | (Term.Apply (Term.Apply Term.bvultbv a1) a2) => (__eo_mk_apply (__eo_mk_apply Term._at_from_bools (__bv_bitblast_ult a1 a2 (Term.Boolean false))) (Term.Binary 0 0))
  | (Term.Apply (Term.Apply Term.bvsltbv a1) a2) => (__eo_mk_apply (__eo_mk_apply Term._at_from_bools (__bv_bitblast_slt_impl (__eo_list_rev Term._at_from_bools a1) (__eo_list_rev Term._at_from_bools a2) (Term.Boolean false))) (Term.Binary 0 0))
  | (Term.Apply (Term.Apply Term.sign_extend n) a1) => (__bv_bitblast_concat a1 (__bv_bitblast_repeat (__bv_bitblast_head (__eo_list_rev Term._at_from_bools a1)) n))
  | a1 => (__eo_ite (__eo_is_bin a1) (__bv_const_to_bitlist_rec a1 (Term.Numeral 0) (__eo_len a1)) (__eo_list_rev Term._at_from_bools (__bv_mk_bitblast_step_var_rec a1 (__eo_add (__bv_bitwidth (__eo_typeof a1)) (Term.Numeral (-1 : eo_lit_Int))))))


partial def __eo_prog_bv_repeat_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.repeat n) a)) b) => (__eo_requires (__eo_list_singleton_elim Term.concat (__eo_ite (__eo_and (__eo_is_z n) (__eo_not (__eo_is_neg n))) (__bv_unfold_repeat_rec n a) (Term.Apply (Term.Apply Term.repeat n) a))) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.repeat n) a)) b))
  | _ => Term.Stuck


partial def __eo_l_1___bv_smulo_elim_rec : Term -> Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | xa, xb, ppc, res, i, nm2 => (__bv_smulo_elim_rec xa xb (__eo_mk_apply (Term.Apply Term.bvor ppc) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add nm2 (__eo_neg i))) (__eo_add nm2 (__eo_neg i))) xa)) (Term.Binary 1 0))) (__eo_mk_apply (Term.Apply Term.bvor res) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add i (Term.Numeral 1))) (__eo_add i (Term.Numeral 1))) xb)) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply Term.bvor ppc) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add nm2 (__eo_neg i))) (__eo_add nm2 (__eo_neg i))) xa)) (Term.Binary 1 0)))) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add i (Term.Numeral 1))) (__eo_add i (Term.Numeral 1))) xb)))))) (Term.Binary 1 0))) (__eo_add i (Term.Numeral 1)) nm2)


partial def __bv_smulo_elim_rec : Term -> Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | xa, xb, ppc, res, nm2, __eo_lv_nm2_2 => (__eo_ite (__eo_eq nm2 __eo_lv_nm2_2) res (__eo_l_1___bv_smulo_elim_rec xa xb ppc res nm2 __eo_lv_nm2_2))


partial def __eo_prog_bv_smulo_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsmulo a) b)) c) => (__eo_requires (__eo_ite (__eo_eq (__bv_bitwidth (__eo_typeof a)) (Term.Numeral 1)) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvand a) (__eo_mk_apply (Term.Apply Term.bvand b) (__eo_nil Term.bvand (__eo_typeof a))))) (Term.Binary 1 1)) (__eo_ite (__eo_eq (__bv_bitwidth (__eo_typeof a)) (Term.Numeral 2)) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))))))) (Term.Binary 1 1)) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.bvor (__bv_smulo_elim_rec (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a)))) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a))))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract (Term.Numeral 1)) (Term.Numeral 1)) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b)))))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a)))))) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract (Term.Numeral 1)) (Term.Numeral 1)) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b))))))))) (Term.Numeral 1) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int))))) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) b)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 1)) a))))))))))) (__eo_nil Term.bvor (__eo_typeof (__bv_smulo_elim_rec (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a)))) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a))))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract (Term.Numeral 1)) (Term.Numeral 1)) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b)))))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_mk_apply (Term.Apply Term.bvxor a) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a))) (__eo_nil Term.bvxor (__eo_typeof a)))))) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract (Term.Numeral 1)) (Term.Numeral 1)) (__eo_mk_apply (Term.Apply Term.bvxor b) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (__eo_mk_apply Term.sign_extend (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) b))) (__eo_nil Term.bvxor (__eo_typeof b))))))))) (Term.Numeral 1) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-2 : eo_lit_Int))))))))) (Term.Binary 1 1)))) c (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsmulo a) b)) c))
  | _ => Term.Stuck


partial def __eo_l_1___bv_umulo_elim_rec : Term -> Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | a, b, uppc, res, i, n => (__eo_cons Term.bvor (__eo_mk_apply (Term.Apply Term.bvand (Term.Apply (Term.Apply (Term.Apply Term.extract i) i) b)) (__eo_mk_apply (Term.Apply Term.bvand uppc) (__eo_nil Term.bvand (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.extract i) i) b))))) (__bv_umulo_elim_rec a b (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) (__eo_neg i))) (__eo_add (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) (__eo_neg i))) a)) (__eo_mk_apply (Term.Apply Term.bvor uppc) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) (__eo_neg i))) (__eo_add (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) (__eo_neg i))) a))))) res (__eo_add i (Term.Numeral 1)) n))


partial def __bv_umulo_elim_rec : Term -> Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | a, b, uppc, res, n, __eo_lv_n_2 => (__eo_ite (__eo_eq n __eo_lv_n_2) res (__eo_l_1___bv_umulo_elim_rec a b uppc res n __eo_lv_n_2))


partial def __eo_prog_bv_umulo_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvumulo a) b)) c) => (__eo_requires (__eo_ite (__eo_eq (__bv_bitwidth (__eo_typeof a)) (Term.Numeral 1)) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply Term.eq (__bv_umulo_elim_rec a b (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_add (__bv_bitwidth (__eo_typeof a)) (Term.Numeral (-1 : eo_lit_Int)))) a) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat a) (Term.Binary 0 0)))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat b) (Term.Binary 0 0)))) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat a) (Term.Binary 0 0))))))))) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.extract (__bv_bitwidth (__eo_typeof a))) (__bv_bitwidth (__eo_typeof a))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat a) (Term.Binary 0 0)))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat b) (Term.Binary 0 0)))) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.concat (Term.Binary 1 0)) (Term.Apply (Term.Apply Term.concat a) (Term.Binary 0 0))))))))))) (Term.Numeral 1) (__bv_bitwidth (__eo_typeof a)))) (Term.Binary 1 1))) c (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvumulo a) b)) c))
  | _ => Term.Stuck


partial def __bv_mk_bitwise_slicing_rec : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | f, c, a, bs, bn, start, (Term.Numeral (-1 : eo_lit_Int)) => (__eo_cons Term.concat (__eo_mk_apply (Term.Apply f (Term.Apply (Term.Apply (Term.Apply Term.extract start) (Term.Numeral 0)) c)) (__eo_mk_apply (Term.Apply f (Term.Apply (Term.Apply (Term.Apply Term.extract start) (Term.Numeral 0)) a)) (__eo_nil f (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.extract start) (Term.Numeral 0)) c))))) (Term.Binary 0 0))
  | f, c, a, (Term.Apply (Term.Apply Term._at_from_bools b) bs), bn, start, __eo_end => (__eo_ite (__eo_eq b bn) (__bv_mk_bitwise_slicing_rec f c a bs b start (__eo_add __eo_end (Term.Numeral (-1 : eo_lit_Int)))) (__eo_cons Term.concat (__eo_mk_apply (__eo_mk_apply f (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.extract start) (__eo_add __eo_end (Term.Numeral 1))) c)) (__eo_mk_apply (__eo_mk_apply f (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.extract start) (__eo_add __eo_end (Term.Numeral 1))) a)) (__eo_nil f (__eo_typeof (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.extract start) (__eo_add __eo_end (Term.Numeral 1))) c))))) (__bv_mk_bitwise_slicing_rec f c a bs b __eo_end (__eo_add __eo_end (Term.Numeral (-1 : eo_lit_Int))))))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __bv_mk_bitwise_slicing : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f a1) a2) => (__eo_list_singleton_elim Term.concat (__eo_requires (__eo_or (__eo_or (__eo_eq f Term.bvand) (__eo_eq f Term.bvor)) (__eo_eq f Term.bvxor)) (Term.Boolean true) (__bv_mk_bitwise_slicing_rec f (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)) (__eo_list_singleton_elim f (__eo_list_erase f (Term.Apply (Term.Apply f a1) a2) (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)))) (__eo_list_rev Term._at_from_bools (__bv_const_to_bitlist_rec (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)) (Term.Numeral 0) (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))))) (__eo_eq (__eo_extract (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2)) (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__eo_len (__bv_get_first_const_child (Term.Apply (Term.Apply f a1) a2))) (Term.Numeral (-1 : eo_lit_Int))))))
  | _ => Term.Stuck


partial def __eo_prog_bv_bitwise_slicing : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__bv_mk_bitwise_slicing a) b (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __eo_prog_bv_bitblast_step : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__bv_mk_bitblast_step a) b (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __eo_prog_bv_poly_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__eo_eq (__poly_mod_coeffs (__get_bv_poly_norm_rec a) (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__bv_bitwidth (__eo_typeof a)))) (__eo_mk_apply Term.int_pow2 (__bv_bitwidth (__eo_typeof a))))) (__poly_mod_coeffs (__get_bv_poly_norm_rec b) (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof a))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof a))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__bv_bitwidth (__eo_typeof a)))) (__eo_mk_apply Term.int_pow2 (__bv_bitwidth (__eo_typeof a)))))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __eo_prog_bv_poly_norm_eq : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq xb1) xb2)) (Term.Apply (Term.Apply Term.eq yb1) yb2)), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvmul cx) (Term.Apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.bvsub __eo_lv_xb1_2) __eo_lv_xb2_2)) one))) (Term.Apply (Term.Apply Term.bvmul cy) (Term.Apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.bvsub __eo_lv_yb1_2) __eo_lv_yb2_2)) __eo_lv_one_2)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq xb1 __eo_lv_xb1_2) (__eo_eq xb2 __eo_lv_xb2_2)) (__eo_eq yb1 __eo_lv_yb1_2)) (__eo_eq yb2 __eo_lv_yb2_2)) (__eo_eq one __eo_lv_one_2)) (Term.Boolean true) (__eo_requires (__eo_to_z one) (Term.Numeral 1) (__eo_requires (__eo_zmod (__eo_to_z cx) (Term.Numeral 2)) (Term.Numeral 1) (__eo_requires (__eo_zmod (__eo_to_z cy) (Term.Numeral 2)) (Term.Numeral 1) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq xb1) xb2)) (Term.Apply (Term.Apply Term.eq yb1) yb2))))))
  | _, _ => Term.Stuck


partial def __get_var_list : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Q xs) G) => xs
  | _ => Term.Stuck


partial def __contains_atomic_term : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f a), x => (__eo_ite (__contains_atomic_term f x) (Term.Boolean true) (__contains_atomic_term a x))
  | x, y => (__eo_eq x y)


partial def __contains_atomic_term_list : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f a), xs => (__eo_ite (__contains_atomic_term_list f xs) (Term.Boolean true) (__contains_atomic_term_list a xs))
  | x, xs => (__eo_not (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs x)))


partial def __contains_atomic_term_list_free_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons x) ys)) a), xs, bvs => (__contains_atomic_term_list_free_rec a xs (__eo_list_concat Term.__eo_List_cons (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bvs))
  | (Term.Apply f a), xs, bvs => (__eo_ite (__contains_atomic_term_list_free_rec f xs bvs) (Term.Boolean true) (__contains_atomic_term_list_free_rec a xs bvs))
  | x, xs, bvs => (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs x)) (Term.Boolean false) (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs x)))


partial def __eo_l_1___substitute : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x, y, z => z


partial def __substitute : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x, y, (Term.Apply (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) => (__eo_requires (__contains_atomic_term_list_free_rec y (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) Term.__eo_List_nil) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply q (__substitute x y (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) (__substitute x y a)))
  | x, y, (Term.Apply f a) => (__eo_mk_apply (__substitute x y f) (__substitute x y a))
  | x, y, __eo_lv_x_2 => (__eo_ite (__eo_eq x __eo_lv_x_2) y (__eo_l_1___substitute x y __eo_lv_x_2))


partial def __substitute_simul : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a), xs, ss => (__eo_requires (__contains_atomic_term_list_free_rec ss (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) Term.__eo_List_nil) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply q (__substitute_simul (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) xs ss)) (__substitute_simul a xs ss)))
  | (Term.Apply f a), xs, ss => (__eo_mk_apply (__substitute_simul f xs ss) (__substitute_simul a xs ss))
  | x, xs, ss => (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs x)) x (__assoc_nil_nth Term.__eo_List_cons ss (__eo_list_find Term.__eo_List_cons xs x)))


partial def __beta_reduce_type : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.FunType T) U), (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) => (__beta_reduce_type U xs)
  | T, Term.__eo_List_nil => T
  | _, _ => Term.Stuck


partial def __beta_reduce : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.lambda (Term.Apply (Term.Apply Term.__eo_List_cons x) xs)) t) a), Term.__eo_List_nil => (__eo_ite (__eo_eq xs Term.__eo_List_nil) (__substitute x a t) (__eo_mk_apply (Term.Apply Term.lambda xs) (__substitute x a t)))
  | (Term.Apply (Term.Apply Term.lambda xs) t), ss => (__substitute_simul t xs ss)
  | (Term.Apply f a), ss => (__beta_reduce f (Term.Apply (Term.Apply Term.__eo_List_cons a) ss))
  | _, _ => Term.Stuck


partial def __str_is_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.seq_empty (Term.Apply Term.Seq U)) => (Term.Boolean true)
  | (Term.String "") => (Term.Boolean true)
  | x => (Term.Boolean false)


partial def __seq_element_of_unit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.seq_unit x) => x
  | _ => Term.Stuck


partial def __str_value_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e)) ss) => (__eo_add (Term.Numeral 1) (__str_value_len ss))
  | (Term.seq_empty (Term.Apply Term.Seq T)) => (Term.Numeral 0)
  | (Term.Apply Term.seq_unit e) => (Term.Numeral 1)
  | s => (__eo_requires (__eo_is_str s) (Term.Boolean true) (__eo_len s))


partial def __char_type_of : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq U) => U
  | _ => Term.Stuck


partial def __str_fixed_len_re : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat r) r1) => (__eo_add (__str_fixed_len_re r) (__str_fixed_len_re r1))
  | Term.re_allchar => (Term.Numeral 1)
  | (Term.Apply (Term.Apply Term.re_range s1) s2) => (Term.Numeral 1)
  | (Term.Apply Term.str_to_re s1) => (__eo_len s1)
  | (Term.Apply (Term.Apply Term.re_union r) r1) => (__eo_ite (__eo_eq r1 Term.re_none) (__str_fixed_len_re r) (__eo_requires (__str_fixed_len_re r1) (__str_fixed_len_re r) (__str_fixed_len_re r)))
  | (Term.Apply (Term.Apply Term.re_inter r) r1) => (__eo_ite (__eo_eq r1 Term.re_all) (__str_fixed_len_re r) (__eo_requires (__str_fixed_len_re r1) (__str_fixed_len_re r) (__str_fixed_len_re r)))
  | _ => Term.Stuck


partial def __str_membership_str : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_in_re s) r) => s
  | _ => Term.Stuck


partial def __str_membership_re : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_in_re s) r) => r
  | _ => Term.Stuck


partial def __re_nullable : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term.re_all => (Term.Boolean true)
  | (Term.Apply Term.str_to_re (Term.String "")) => (Term.Boolean true)
  | (Term.Apply Term.re_mult r) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.re_union r) rr) => (__eo_or (__re_nullable r) (__re_nullable rr))
  | (Term.Apply (Term.Apply Term.re_inter r) rr) => (__eo_and (__re_nullable r) (__re_nullable rr))
  | (Term.Apply (Term.Apply Term.re_concat r) rr) => (__eo_and (__re_nullable r) (__re_nullable rr))
  | (Term.Apply Term.re_comp r) => (__eo_not (__re_nullable r))
  | r => (Term.Boolean false)


partial def __eo_l_4___re_ac_merge : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, r1, r2 => (__eo_mk_apply (Term.Apply f r1) (__eo_mk_apply (Term.Apply f r2) (__eo_nil f Term.RegLan)))


partial def __eo_l_3___re_ac_merge : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, r2, (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_ite (__eo_is_neg (__eo_list_find f (Term.Apply (Term.Apply f r1) rr1) r2)) (__eo_cons f r2 (Term.Apply (Term.Apply f r1) rr1)) (Term.Apply (Term.Apply f r1) rr1)) (__eo_l_4___re_ac_merge f r2 (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_4___re_ac_merge __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_2___re_ac_merge : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1), r2 => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_ite (__eo_is_neg (__eo_list_find f (Term.Apply (Term.Apply f r1) rr1) r2)) (__eo_cons f r2 (Term.Apply (Term.Apply f r1) rr1)) (Term.Apply (Term.Apply f r1) rr1)) (__eo_l_3___re_ac_merge f (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1) r2))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_3___re_ac_merge __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_1___re_ac_merge : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1), (Term.Apply (Term.Apply __eo_lv_f_3 r2) rr2) => (__eo_ite (__eo_and (__eo_eq f __eo_lv_f_2) (__eo_eq f __eo_lv_f_3)) (__eo_list_concat f (__eo_list_diff f (Term.Apply (Term.Apply f r1) rr1) (Term.Apply (Term.Apply f r2) rr2)) (Term.Apply (Term.Apply f r2) rr2)) (__eo_l_2___re_ac_merge f (Term.Apply (Term.Apply __eo_lv_f_2 r1) rr1) (Term.Apply (Term.Apply __eo_lv_f_3 r2) rr2)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_2___re_ac_merge __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __re_ac_merge : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.re_union, Term.re_none, r1 => r1
  | Term.re_inter, Term.re_none, r1 => Term.re_none
  | f, r1, __eo_lv_r1_2 => (__eo_ite (__eo_eq r1 __eo_lv_r1_2) r1 (__eo_l_1___re_ac_merge f r1 __eo_lv_r1_2))


partial def __re_concat_merge : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat r1) rr1), (Term.Apply (Term.Apply Term.re_concat r2) rr2) => (__eo_list_concat Term.re_concat (Term.Apply (Term.Apply Term.re_concat r1) rr1) (Term.Apply (Term.Apply Term.re_concat r2) rr2))
  | Term.re_none, r1 => Term.re_none
  | r1, (Term.Apply (Term.Apply Term.re_concat r2) rr2) => (__eo_cons Term.re_concat r1 (Term.Apply (Term.Apply Term.re_concat r2) rr2))
  | (Term.Apply Term.str_to_re (Term.String "")), r1 => r1
  | r1, (Term.Apply Term.str_to_re (Term.String "")) => r1
  | r1, r2 => (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply (Term.Apply Term.re_concat r2) (Term.Apply Term.str_to_re (Term.String ""))))


partial def __derivative : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c, (Term.Apply (Term.Apply Term.re_union r) rr) => (__re_ac_merge Term.re_union (__derivative c r) (__derivative c rr))
  | c, (Term.Apply (Term.Apply Term.re_concat r) rr) => (__eo_ite (__re_nullable r) (__re_ac_merge Term.re_union (__derivative c rr) (__re_concat_merge (__derivative c r) rr)) (__re_concat_merge (__derivative c r) rr))
  | c, (Term.Apply (Term.Apply Term.re_inter r) rr) => (__re_ac_merge Term.re_inter (__derivative c r) (__derivative c rr))
  | c, (Term.Apply Term.re_comp r) => (__eo_mk_apply Term.re_comp (__derivative c r))
  | c, (Term.Apply Term.re_mult r) => (__re_concat_merge (__derivative c r) (Term.Apply Term.re_mult r))
  | c, (Term.Apply Term.str_to_re (Term.String "")) => Term.re_none
  | c, (Term.Apply Term.str_to_re s1) => (__eo_ite (__eo_is_eq (__eo_extract s1 (Term.Numeral 0) (Term.Numeral 0)) c) (__eo_mk_apply Term.str_to_re (__eo_extract s1 (Term.Numeral 1) (__eo_add (Term.Numeral (-1 : eo_lit_Int)) (__eo_len s1)))) Term.re_none)
  | c, (Term.Apply (Term.Apply Term.re_range s1) s2) => (__eo_ite (__eo_and (__eo_ite (__eo_eq (__eo_to_z c) (__eo_to_z s1)) (Term.Boolean true) (__eo_gt (__eo_to_z c) (__eo_to_z s1))) (__eo_ite (__eo_eq (__eo_to_z s2) (__eo_to_z c)) (Term.Boolean true) (__eo_gt (__eo_to_z s2) (__eo_to_z c)))) (Term.Apply Term.str_to_re (Term.String "")) Term.re_none)
  | c, Term.re_none => Term.re_none
  | c, Term.re_all => Term.re_all
  | c, Term.re_allchar => (Term.Apply Term.str_to_re (Term.String ""))
  | _, _ => Term.Stuck


partial def __str_eval_str_in_re : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.String ""), r => (__re_nullable r)
  | s, Term.re_none => (Term.Boolean false)
  | s, r => (__str_eval_str_in_re (__eo_extract s (Term.Numeral 1) (__eo_add (Term.Numeral (-1 : eo_lit_Int)) (__eo_len s))) (__derivative (__eo_extract s (Term.Numeral 0) (Term.Numeral 0)) r))


partial def __str_first_match_rec_smallest : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, r, m, lens => (__eo_ite (__str_eval_str_in_re (__eo_extract s (Term.Numeral 0) (__eo_add m (Term.Numeral (-1 : eo_lit_Int)))) r) m (__eo_requires (__eo_eq m lens) (Term.Boolean false) (__str_first_match_rec_smallest s r (__eo_add m (Term.Numeral 1)) lens)))


partial def __str_first_match_rec : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, r, rs, n, lens => (__eo_ite (__str_eval_str_in_re s rs) (__eo_mk_apply (Term.Apply Term._at__at_pair n) (__eo_add n (__str_first_match_rec_smallest s r (Term.Numeral 0) lens))) (__eo_ite (__eo_eq lens (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at__at_pair (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) (__str_first_match_rec (__eo_extract s (Term.Numeral 1) (__eo_add lens (Term.Numeral (-1 : eo_lit_Int)))) r rs (__eo_add n (Term.Numeral 1)) (__eo_add lens (Term.Numeral (-1 : eo_lit_Int))))))


partial def __str_unify_split : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, s, (Term.Boolean true) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len t)) (Term.Apply Term.str_len s))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t)) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t))))
  | t, s, (Term.Boolean false) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len t)) (Term.Apply Term.str_len s))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Apply Term.str_len s)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t)) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply Term.str_len t)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t))))
  | _, _, _ => Term.Stuck


partial def __str_nary_intro : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) ss) => (Term.Apply (Term.Apply Term.str_concat t) ss)
  | t => (__eo_ite (__eo_eq t (__seq_empty (__eo_typeof t))) t (__eo_cons Term.str_concat t (__seq_empty (__eo_typeof t))))


partial def __re_nary_intro : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat t) ss) => (Term.Apply (Term.Apply Term.re_concat t) ss)
  | (Term.Apply Term.str_to_re (Term.String "")) => (Term.Apply Term.str_to_re (Term.String ""))
  | t => (__eo_cons Term.re_concat t (Term.Apply Term.str_to_re (Term.String "")))


partial def __str_nary_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) ss) => (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (Term.Apply (Term.Apply Term.str_concat t) ss))
  | t => (__eo_requires t (__seq_empty (__eo_typeof t)) t)


partial def __re_nary_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat t) ss) => (__eo_ite (__eo_eq ss (Term.Apply Term.str_to_re (Term.String ""))) t (Term.Apply (Term.Apply Term.re_concat t) ss))
  | t => t


partial def __str_reduction_pred : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_contains x) y) => (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply Term.str_contains x) y))) (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply Term.str_len y))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len y))) y))) (Term.Boolean false)))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m) => (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len x)) n)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt m) (Term.Numeral 0))) (Term.Boolean true))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq x) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n)))) n)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))))))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))))))) (Term.Numeral 0))) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m)))) m)) (Term.Boolean true)))))) (__eo_mk_apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) m))) (__seq_empty (__eo_typeof x))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n) => (__eo_mk_apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.gt n) (Term.Apply Term.str_len x))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.gt (Term.Numeral 0)) n)) (Term.Boolean false))))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.eq y) (__seq_empty (__eo_typeof x)))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n))) n)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat y) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n)))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0))))))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_contains (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len y)) (Term.Numeral 1)))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0))))))))) y))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n))) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))) y) (Term.Numeral 0)))))) (Term.Numeral 0))))) (Term.Boolean true))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z) => (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.eq y) (__seq_empty (__eo_typeof y)))) (__eo_mk_apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z))) (__eo_mk_apply (Term.Apply Term.str_concat z) (__eo_mk_apply (Term.Apply Term.str_concat x) (__eo_nil Term.str_concat (__eo_typeof z)))))) (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.str_contains x) y)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq x) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat y) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat z) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_contains (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len y)) (Term.Numeral 1)))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))))))) y))) (Term.Boolean true))))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z))) x)))
  | (Term.Apply Term.str_from_int n) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_from_int n)))) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq n) (Term.Apply (Term.Apply Term._at_strings_itos_result n) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_from_int n)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_strings_itos_result n) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_from_int n)))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_strings_itos_result n) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_from_int n))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult (Term.Numeral 10)) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term._at_strings_itos_result n) (Term.Var "@var.str_index" Term.Int))) (Term.Numeral 1)))) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_from_int n))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_from_int n)))) (Term.Numeral 1))) (Term.Boolean true)))) (Term.Numeral 1)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_from_int n))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Numeral 10))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq n) (Term.Apply (Term.Apply Term._at_strings_itos_result n) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))) (Term.Boolean true))))) (Term.Boolean false)))))) (Term.Boolean true)))))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply Term.str_from_int n))) (Term.String "")))
  | (Term.Apply Term.str_to_int s) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.lt (Term._at_purify (Term.Apply Term.str_to_int s))) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply Term.str_to_int s))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq s) (Term.String ""))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply Term._at_strings_stoi_non_digit s)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply Term._at_strings_stoi_non_digit s)) (Term.Apply Term.str_len s))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply Term._at_strings_stoi_non_digit s)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply Term._at_strings_stoi_non_digit s)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Numeral 10))) (Term.Boolean false)))) (Term.Boolean true))))) (Term.Boolean false)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply Term.str_to_int s))) (Term.Apply (Term.Apply Term._at_strings_stoi_result s) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_strings_stoi_result s) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len s)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_strings_stoi_result s) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult (Term.Numeral 10)) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term._at_strings_stoi_result s) (Term.Var "@var.str_index" Term.Int))) (Term.Numeral 1)))) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 48))) (Term.Numeral 10))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term._at_purify (Term.Apply Term.str_to_int s))) (Term.Apply (Term.Apply Term._at_strings_stoi_result s) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))) (Term.Boolean true))))) (Term.Boolean false)))))) (Term.Boolean true))))))
  | (Term.Apply (Term.Apply Term.seq_nth x) n) => (__eo_mk_apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len x)) n)) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq x) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit (Term._at_purify (Term.Apply (Term.Apply Term.seq_nth x) n)))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n)))) n)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus n) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))) (Term.Boolean true)))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_update x) n) y) => (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len x)) n)) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_update x) n) y))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n)))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.str_substr x) (__eo_mk_apply (Term.Apply Term.plus n) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))) (Term.Numeral 0)))) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (__eo_mk_apply (Term.Apply Term.plus n) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq x) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr x) n) (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.str_substr x) (__eo_mk_apply (Term.Apply Term.plus n) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))) (Term.Numeral 0)))) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (__eo_mk_apply (Term.Apply Term.plus n) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n))))))))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) n)))) n)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))) (__eo_mk_apply Term.str_len (Term._at_purify (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr x) n) (__eo_mk_apply Term.str_len (__eo_ite (__eo_is_eq (__str_value_len y) (Term.Numeral 1)) y (Term.Apply (Term.Apply (Term.Apply Term.str_substr y) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) n))))))))) (Term.Boolean true)))))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_update x) n) y))) x))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z) => (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.eq y) (__seq_empty (__eo_typeof x)))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z))) x)) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term._at_strings_num_occur x) y)) (Term.Numeral 0))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z))) (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z)) (Term.Numeral 0)))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z)) (Term.Apply (Term.Apply Term._at_strings_num_occur x) y))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Apply (Term.Apply Term._at_strings_num_occur x) y))) (Term.Apply Term.str_len x)))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Numeral 0))) (Term.Numeral 0))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Apply (Term.Apply Term._at_strings_num_occur x) y)))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term._at_strings_num_occur x) y)))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int)))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z)) (Term.Var "@var.str_index" Term.Int))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int))))) (__eo_mk_apply (Term.Apply Term.str_concat z) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x) y) z)) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (__eo_nil Term.str_concat (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int))))))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index x) y) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0))))) (Term.Boolean true))))) (Term.Boolean false)))))) (Term.Boolean true))))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re s) r) t) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re s) r) t))) s)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq s) (Term.Apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1)))))) (Term.String "")))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0)))))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_length" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_length" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_length" Term.Int)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))))))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0)))))) (Term.Numeral 0)) (Term.Var "@var.str_length" Term.Int))) r))) (Term.Boolean false)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_in_re (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0)))))) r)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re s) r) t))) (Term.Apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) (Term.Numeral 0))))) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 1)))))) (Term.String "")))))) (Term.Boolean true)))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t))) s)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply (Term.Apply Term._at_strings_num_occur_re s) r)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t))) (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) (Term.Apply (Term.Apply Term._at_strings_num_occur_re s) r))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Apply (Term.Apply Term._at_strings_num_occur_re s) r))) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Numeral 0))) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Apply (Term.Apply Term._at_strings_num_occur_re s) r))) (Term.Apply Term.str_len s))) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term._at_strings_num_occur_re s) r)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.gt (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int))))) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int)))))) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String ""))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_length" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.gt (Term.Var "@var.str_length" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_length" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int))))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int)))) (Term.Var "@var.str_length" Term.Int))) r))) (Term.Boolean false)))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) (Term.Apply (Term.Apply Term.re_diff r) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply (Term.Apply (Term.Apply Term._at_strings_occur_index_re s) r) (Term.Var "@var.str_index" Term.Int))))) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat (Term.Apply (Term._at_strings_replace_all_result (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.String "")))))) (Term.Boolean true)))))) (Term.Boolean false)))))) (Term.Boolean true))))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.gt n) (Term.Apply Term.str_len s))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.gt (Term.Numeral 0)) n)) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.str_in_re (Term.String "")) r)) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) n)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_length" Term.Int)) Term.__eo_List_nil))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) n))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply Term.str_len s)) (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.gt (Term.Var "@var.str_length" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_length" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Var "@var.str_index" Term.Int))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Var "@var.str_length" Term.Int))) r))) (Term.Boolean false)))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) n)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_length" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_length" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_length" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)))))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))) (Term.Var "@var.str_length" Term.Int))) r))) (Term.Boolean false))))))) (Term.Boolean true)))) (Term.Boolean false)))) (Term.Boolean true)))))
  | (Term.Apply (Term.Apply Term.str_leq s) t) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq s) t)) (Term._at_purify (Term.Apply (Term.Apply Term.str_leq s) t))) (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len s)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len t)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0)) (Term.Var "@var.str_index" Term.Int))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply (Term.Apply Term.ite (Term._at_purify (Term.Apply (Term.Apply Term.str_leq s) t))) (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1))))) (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))))) (Term.Boolean false)))))))))
  | (Term.Apply Term.str_to_lower s) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_to_lower s))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_to_lower s)))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_to_lower s))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Numeral 65)) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 90))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.plus (Term.Numeral 32)) (Term.Numeral 0)))) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))))) (Term.Boolean false)))))) (Term.Boolean true)))
  | (Term.Apply Term.str_to_upper s) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_to_upper s))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_to_upper s)))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_to_upper s))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Numeral 97)) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Numeral 122))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.plus (Term.Numeral (-32 : eo_lit_Int))) (Term.Numeral 0)))) (Term.Apply Term.str_to_code (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1)))))) (Term.Boolean false)))))) (Term.Boolean true)))
  | (Term.Apply Term.str_rev x) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len x)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_rev x))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Apply Term.str_len (Term._at_purify (Term.Apply Term.str_rev x)))))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term._at_purify (Term.Apply Term.str_rev x))) (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) (Term.Numeral 1)))) (Term.Boolean false)))))) (Term.Boolean true)))
  | _ => Term.Stuck


partial def __mk_str_eager_reduction : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.str_from_code n) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Numeral 0)) n)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt n) (Term.Numeral 196608))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.eq n) (Term.Apply Term.str_to_code (Term._at_purify (Term.Apply Term.str_from_code n))))) (Term.Apply (Term.Apply Term.eq (Term._at_purify (Term.Apply Term.str_from_code n))) (Term.String "")))
  | (Term.Apply Term.str_to_code s) => (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_to_code s)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply Term.str_to_code s)) (Term.Numeral 196608))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_code s)) (Term.Numeral (-1 : eo_lit_Int))))
  | (Term.Apply Term.str_to_int s) => (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_to_int s)) (Term.Numeral (-1 : eo_lit_Int)))
  | (Term.Apply (Term.Apply Term.str_contains x) y) => (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.str_contains x) y)) (__eo_mk_apply (Term.Apply Term.eq x) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))) (__eo_mk_apply (Term.Apply Term.str_concat y) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len x)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len y)) (Term.Numeral 0))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr x) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) (Term.Numeral 0))))))))))) (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n)) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n)) n)) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n)) (Term.Apply Term.str_len x))) (Term.Boolean true)))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n) => (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) n)) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) (Term.Apply Term.str_len s))) (Term.Boolean true)))
  | (Term.Apply (Term.Apply Term.str_in_re s) r) => (__eo_mk_apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.str_in_re s) r)) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (__str_fixed_len_re r)))
  | _ => Term.Stuck


partial def __re_unfold_pos_concat_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply Term.str_to_re (Term.String "")), ro, i => (Term.Apply (Term.Apply Term._at__at_pair (Term.String "")) (Term.Boolean true))
  | t, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s)) r2), ro, i => (__eo_mk_apply (__eo_mk_apply Term._at__at_pair (__eo_cons Term.str_concat s (__pair_first (__re_unfold_pos_concat_rec t r2 ro (__eo_add i (Term.Numeral 1)))))) (__pair_second (__re_unfold_pos_concat_rec t r2 ro (__eo_add i (Term.Numeral 1)))))
  | t, (Term.Apply (Term.Apply Term.re_concat r1) r2), ro, i => (__eo_mk_apply (__eo_mk_apply Term._at__at_pair (__eo_cons Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term._at_re_unfold_pos_component t) ro) i) (__pair_first (__re_unfold_pos_concat_rec t r2 ro (__eo_add i (Term.Numeral 1)))))) (__eo_cons Term.and (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term._at_re_unfold_pos_component t) ro) i)) r1) (__pair_second (__re_unfold_pos_concat_rec t r2 ro (__eo_add i (Term.Numeral 1))))))
  | _, _, _, _ => Term.Stuck


partial def __str_flatten_word : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.String "") => (Term.String "")
  | t => (__eo_cons Term.str_concat (__eo_extract t (Term.Numeral 0) (Term.Numeral 0)) (__str_flatten_word (__eo_extract t (Term.Numeral 1) (__eo_len t))))


partial def __str_flatten : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) tail) => (__eo_ite (__eo_is_eq (__eo_is_neg (__eo_add (Term.Numeral 1) (__eo_neg (__eo_len t)))) (Term.Boolean true)) (__eo_list_concat Term.str_concat (__str_flatten_word t) (__str_flatten tail)) (__eo_cons Term.str_concat t (__str_flatten tail)))
  | t => (__eo_requires t (__seq_empty (__eo_typeof t)) t)


partial def __str_collect_acc : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) tail) => (__eo_ite (__eo_is_eq (__eo_len t) (Term.Numeral 1)) (__eo_ite (__eo_eq (__pair_first (__str_collect_acc tail)) (Term.String "")) (__eo_mk_apply (Term.Apply Term._at__at_pair t) (__pair_second (__str_collect_acc tail))) (__eo_mk_apply (__eo_mk_apply Term._at__at_pair (__eo_concat t (__pair_first (__str_collect_acc tail)))) (__pair_second (__str_collect_acc tail)))) (Term.Apply (Term.Apply Term._at__at_pair (Term.String "")) (Term.Apply (Term.Apply Term.str_concat t) tail)))
  | (Term.String "") => (Term.Apply (Term.Apply Term._at__at_pair (Term.String "")) (Term.String ""))
  | _ => Term.Stuck


partial def __str_collect : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) s) => (__eo_ite (__eo_eq (__pair_first (__str_collect_acc (Term.Apply (Term.Apply Term.str_concat t) s))) (Term.String "")) (__eo_cons Term.str_concat t (__str_collect s)) (__eo_cons Term.str_concat (__pair_first (__str_collect_acc (Term.Apply (Term.Apply Term.str_concat t) s))) (__str_collect (__pair_second (__str_collect_acc (Term.Apply (Term.Apply Term.str_concat t) s))))))
  | t => (__eo_requires t (__seq_empty (__eo_typeof t)) t)


partial def __eo_l_1___str_strip_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Apply (Term.Apply Term._at__at_pair t) s)


partial def __str_strip_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) t2), (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) s2) => (__eo_ite (__eo_eq t __eo_lv_t_2) (__str_strip_prefix t2 s2) (__eo_l_1___str_strip_prefix (Term.Apply (Term.Apply Term.str_concat t) t2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) s2)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___str_strip_prefix __eo_dv_1 __eo_dv_2)


partial def __str_mk_re_loop_elim_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Numeral 0), (Term.Numeral 0), r, rr => (__eo_cons Term.re_union (__eo_list_singleton_elim Term.re_concat rr) Term.re_none)
  | (Term.Numeral 0), d, r, rr => (__eo_cons Term.re_union (__eo_list_singleton_elim Term.re_concat rr) (__str_mk_re_loop_elim_rec (Term.Numeral 0) (__eo_add d (Term.Numeral (-1 : eo_lit_Int))) r (Term.Apply (Term.Apply Term.re_concat r) rr)))
  | n, d, r, rr => (__str_mk_re_loop_elim_rec (__eo_add n (Term.Numeral (-1 : eo_lit_Int))) d r (Term.Apply (Term.Apply Term.re_concat r) rr))


partial def __str_mk_str_in_re_concat_star_char : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), r => (__eo_cons Term.and (Term.Apply (Term.Apply Term.str_in_re s1) r) (__str_mk_str_in_re_concat_star_char s2 r))
  | (Term.String ""), r => (Term.Boolean true)
  | _, _ => Term.Stuck


partial def __str_mk_str_in_re_sigma_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, (Term.Apply Term.str_to_re (Term.String "")), n, b => (__eo_ite b (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) n) (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) n))
  | s, (Term.Apply (Term.Apply Term.re_concat Term.re_allchar) r), n, b => (__str_mk_str_in_re_sigma_rec s r (__eo_add n (Term.Numeral 1)) b)
  | s, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) r), n, b => (__str_mk_str_in_re_sigma_rec s r n (Term.Boolean false))
  | _, _, _, _ => Term.Stuck


partial def __str_mk_str_in_re_sigma_star_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s, (Term.Apply Term.str_to_re (Term.String "")), n => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod (Term.Apply Term.str_len s)) n)) (Term.Numeral 0))
  | s, (Term.Apply (Term.Apply Term.re_concat Term.re_allchar) r), n => (__str_mk_str_in_re_sigma_star_rec s r (__eo_add n (Term.Numeral 1)))
  | _, _, _ => Term.Stuck


partial def __re_str_to_flat_form : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | rev, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s)) r2) => (__eo_cons Term.re_concat (__eo_mk_apply Term.str_to_re (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_flatten (__str_nary_intro s)))) (__re_str_to_flat_form rev r2))
  | rev, (Term.Apply (Term.Apply Term.re_concat r1) r2) => (__eo_cons Term.re_concat r1 (__re_str_to_flat_form rev r2))
  | rev, r1 => r1


partial def __re_str_from_flat_form : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | rev, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s)) r2) => (__eo_cons Term.re_concat (__eo_mk_apply Term.str_to_re (__str_nary_elim (__str_collect (__eo_ite rev (__eo_list_rev Term.str_concat s) s)))) (__re_str_from_flat_form rev r2))
  | rev, (Term.Apply (Term.Apply Term.re_concat r1) r2) => (__eo_cons Term.re_concat r1 (__re_str_from_flat_form rev r2))
  | rev, r1 => r1


partial def __str_re_includes_lhs_union : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_union r1) r2), r3 => (__eo_ite (__str_re_includes r1 r3) (Term.Boolean true) (__str_re_includes_lhs_union r2 r3))
  | r1, r3 => (Term.Boolean false)


partial def __str_re_includes_rhs_inter : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | r1, (Term.Apply (Term.Apply Term.re_inter r3) r2) => (__eo_ite (__str_re_includes r1 r3) (Term.Boolean true) (__str_re_includes_rhs_inter r1 r2))
  | r1, r3 => (Term.Boolean false)


partial def __str_maybe_get_star_body : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.re_mult r) => r
  | r => r


partial def __str_re_includes_lhs_star : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.re_mult r1), r2 => (__eo_ite (__eo_eq r1 Term.re_allchar) (Term.Boolean true) (__str_re_includes r1 (__str_maybe_get_star_body r2)))
  | r1, r2 => (Term.Boolean false)


partial def __str_re_includes_is_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | r1, (Term.Apply (Term.Apply Term.re_inter r3) r2) => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.re_union r1) r2), r3 => (Term.Boolean false)
  | (Term.Apply Term.re_mult r1), r3 => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.re_concat r1) r2), r3 => (Term.Boolean true)
  | r3, (Term.Apply (Term.Apply Term.re_concat r1) r2) => (Term.Boolean true)
  | r1, r3 => (Term.Boolean false)


partial def __re_is_unbound_wildcard : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) r2) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.re_concat Term.re_allchar) r2) => (__re_is_unbound_wildcard r2)
  | r1 => (Term.Boolean false)


partial def __eo_l_1___str_re_includes_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.Apply (Term.Apply Term.str_concat s1) s2))) r2), r3 => (__str_re_includes_rec (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s2)) r2)) r3)
  | (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.String ""))) r2), r3 => (__str_re_includes_rec r2 r3)
  | r1, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.Apply (Term.Apply Term.str_concat s1) s2))) r4) => (__str_re_includes_rec r1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s2)) r4)))
  | r1, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.String ""))) r4) => (__str_re_includes_rec r1 r4)
  | (Term.Apply (Term.Apply Term.re_concat r1) r2), (Term.Apply (Term.Apply Term.re_concat r3) r4) => (__eo_ite (__eo_ite (__str_re_includes (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) r1)) (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) r3))) (__str_re_includes_rec r2 r4) (Term.Boolean false)) (Term.Boolean true) (__eo_ite (__eo_ite (__re_is_unbound_wildcard (Term.Apply (Term.Apply Term.re_concat r1) r2)) (__str_re_includes_rec (Term.Apply (Term.Apply Term.re_concat r1) r2) r4) (Term.Boolean false)) (Term.Boolean true) (__eo_ite (__eo_ite (__eo_eq r1 (Term.Apply Term.re_mult Term.re_allchar)) (__str_re_includes_rec r2 (Term.Apply (Term.Apply Term.re_concat r3) r4)) (Term.Boolean false)) (Term.Boolean true) (Term.Boolean false))))
  | (Term.Apply (Term.Apply Term.re_concat r1) r2), (Term.Apply Term.str_to_re (Term.String "")) => (__eo_and (__eo_eq r1 (Term.Apply Term.re_mult Term.re_allchar)) (__eo_eq r2 (Term.Apply Term.str_to_re (Term.String ""))))
  | r1, r3 => (Term.Boolean false)


partial def __str_re_includes_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | r1, __eo_lv_r1_2 => (__eo_ite (__eo_eq r1 __eo_lv_r1_2) (Term.Boolean true) (__eo_l_1___str_re_includes_rec r1 __eo_lv_r1_2))


partial def __eo_l_1___str_re_includes : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | r1, (Term.Apply Term.str_to_re s1) => (__str_eval_str_in_re s1 r1)
  | (Term.Apply Term.str_to_re s1), r1 => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.re_range s1) s2), (Term.Apply (Term.Apply Term.re_range s3) s4) => (__eo_requires (__eo_is_neg (__eo_to_z s1)) (Term.Boolean false) (__eo_requires (__eo_is_neg (__eo_to_z s2)) (Term.Boolean false) (__eo_requires (__eo_is_neg (__eo_to_z s3)) (Term.Boolean false) (__eo_requires (__eo_is_neg (__eo_to_z s4)) (Term.Boolean false) (__eo_and (__eo_and (__eo_and (__eo_ite (__eo_eq (__eo_to_z s2) (__eo_to_z s3)) (Term.Boolean true) (__eo_gt (__eo_to_z s2) (__eo_to_z s3))) (__eo_ite (__eo_eq (__eo_to_z s3) (__eo_to_z s1)) (Term.Boolean true) (__eo_gt (__eo_to_z s3) (__eo_to_z s1)))) (__eo_ite (__eo_eq (__eo_to_z s2) (__eo_to_z s4)) (Term.Boolean true) (__eo_gt (__eo_to_z s2) (__eo_to_z s4)))) (__eo_ite (__eo_eq (__eo_to_z s4) (__eo_to_z s1)) (Term.Boolean true) (__eo_gt (__eo_to_z s4) (__eo_to_z s1))))))))
  | r1, r3 => (__eo_ite (__eo_eq (__str_re_includes_lhs_union r1 r3) (Term.Boolean true)) (Term.Boolean true) (__eo_ite (__eo_eq (__str_re_includes_rhs_inter r1 r3) (Term.Boolean true)) (Term.Boolean true) (__eo_ite (__eo_eq (__str_re_includes_lhs_star r1 r3) (Term.Boolean true)) (Term.Boolean true) (__eo_ite (__str_re_includes_is_rec r1 r3) (__str_re_includes_rec (__re_str_to_flat_form (Term.Boolean false) (__re_nary_intro r1)) (__re_str_to_flat_form (Term.Boolean false) (__re_nary_intro r3))) (Term.Boolean false)))))


partial def __str_re_includes : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | r1, __eo_lv_r1_2 => (__eo_ite (__eo_eq r1 __eo_lv_r1_2) (Term.Boolean true) (__eo_l_1___str_re_includes r1 __eo_lv_r1_2))


partial def __str_arith_entail_simple : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.str_len s) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.plus n1) n2) => (__eo_ite (__str_arith_entail_simple n1) (__str_arith_entail_simple n2) (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.mult n1) n2) => (__eo_ite (__str_arith_entail_simple n1) (__str_arith_entail_simple n2) (Term.Boolean false))
  | n1 => (__eo_not (__eo_is_neg n1))


partial def __str_arith_entail_simple_pred : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.geq n) m) => (__str_arith_entail_simple (__arith_poly_to_term_rec (__get_arith_poly_norm (Term.Apply (Term.Apply Term.neg n) m))))
  | (Term.Apply (Term.Apply Term.gt n) m) => (__str_arith_entail_simple (__arith_poly_to_term_rec (__get_arith_poly_norm (Term.Apply (Term.Apply Term.neg n) (Term.Apply (Term.Apply Term.plus m) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))))
  | _ => Term.Stuck


partial def __str_arith_entail_is_approx_len : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n1) n2), n, isUnder => (__eo_ite (__eo_eq n n2) (__eo_ite isUnder (__eo_and (__str_arith_entail_simple n1) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))))) (__str_arith_entail_simple n2)) (__eo_ite (__eo_eq n (Term.Apply Term.str_len s)) (__eo_not isUnder) (__eo_ite (__eo_eq n (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n1)) (__eo_ite isUnder (__eo_and (__str_arith_entail_simple n1) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))) (Term.Apply Term.str_len s)))) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) n1))) (Term.Boolean false))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace s) t) r), n, isUnder => (__eo_ite (__eo_eq n (Term.Apply Term.str_len s)) (__eo_ite isUnder (__eo_or (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len r)) (Term.Apply Term.str_len t))) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len r)) (Term.Apply Term.str_len s)))) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len t)) (Term.Apply Term.str_len r)))) (__eo_ite (__eo_eq n (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len s)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len r)) (Term.Numeral 0)))) (__eo_not isUnder) (__eo_ite (__eo_eq n (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t))) isUnder (Term.Boolean false))))
  | (Term.Apply Term.str_from_int n1), n, isUnder => (__eo_ite (__eo_eq n (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))) (__eo_and (__eo_not isUnder) (__str_arith_entail_simple n1)) (__eo_ite (__eo_eq n n1) (__eo_and (__eo_not isUnder) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.gt n1) (Term.Numeral 0)))) (__eo_ite (__eo_eq n (Term.Numeral 1)) (__eo_and isUnder (__str_arith_entail_simple n1)) (Term.Boolean false))))
  | _, _, _ => Term.Stuck


partial def __eo_l_1___str_arith_entail_is_approx : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.str_len s), n1, isUnder => (__str_arith_entail_is_approx_len s n1 isUnder)
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof s) t) n3), n1, isUnder => (__eo_ite (__eo_eq n1 (Term.Numeral (-1 : eo_lit_Int))) isUnder (__eo_ite (__eo_eq n1 (Term.Apply Term.str_len s)) (__eo_not isUnder) (__eo_ite (__eo_eq n1 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t))) (__eo_and (__eo_not isUnder) (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t)))) (Term.Boolean false))))
  | (Term.Apply Term.str_to_int s), n1, isUnder => (__eo_ite (__eo_eq n1 (Term.Numeral (-1 : eo_lit_Int))) isUnder (Term.Boolean false))
  | (Term.Apply (Term.Apply Term.plus n1) n2), (Term.Apply (Term.Apply Term.plus n3) n4), isUnder => (__eo_and (__str_arith_entail_is_approx n1 n3 isUnder) (__str_arith_entail_is_approx n2 n4 isUnder))
  | (Term.Apply (Term.Apply Term.mult n1) (Term.Apply (Term.Apply Term.mult n3) (Term.Numeral 1))), (Term.Apply (Term.Apply Term.mult __eo_lv_n1_2) (Term.Apply (Term.Apply Term.mult n5) (Term.Numeral 1))), isUnder => (__eo_requires (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (__eo_ite (__eo_is_neg n1) (__str_arith_entail_is_approx n3 n5 (__eo_not isUnder)) (__str_arith_entail_is_approx n3 n5 isUnder)))
  | _, _, _ => Term.Stuck


partial def __str_arith_entail_is_approx : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | n1, __eo_lv_n1_2, isUnder => (__eo_ite (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (__eo_l_1___str_arith_entail_is_approx n1 __eo_lv_n1_2 isUnder))


partial def __str_re_consume_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.Apply (Term.Apply Term.str_concat s3) s4))) r2), Term._at__at_result_null, rev => (__eo_ite (__eo_eq s1 s3) (__str_re_consume_rec s2 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s4)) r2) Term._at__at_result_null rev) (__eo_ite (__eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1)) (__eo_is_eq (__eo_len s3) (Term.Numeral 1))) (Term.Boolean false) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.Apply (Term.Apply Term.str_concat s3) s4))) r2))))
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.String ""))) r2), Term._at__at_result_null, rev => (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r2 Term._at__at_result_null rev)
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat (Term.Apply (Term.Apply Term.re_range s3) s5)) r2), Term._at__at_result_null, rev => (__eo_ite (__eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1)) (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) (__eo_is_eq (__eo_len s5) (Term.Numeral 1)))) (__eo_ite (__str_eval_str_in_re s1 (Term.Apply (Term.Apply Term.re_range s3) s5)) (__str_re_consume_rec s2 r2 Term._at__at_result_null rev) (Term.Boolean false)) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply (Term.Apply Term.re_range s3) s5)) r2)))
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat Term.re_allchar) r2), Term._at__at_result_null, rev => (__eo_ite (__eo_is_eq (__eo_len s1) (Term.Numeral 1)) (__str_re_consume_rec s2 r2 Term._at__at_result_null rev) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat Term.re_allchar) r2)))
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r3)) r2), Term._at__at_result_null, rev => (__eo_ite (__eo_eq (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r3)) (__re_nary_intro r3))) Term._at__at_result_null rev) (Term.Boolean false)) (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r2 Term._at__at_result_null rev) (__eo_ite (__eo_eq (__str_membership_re (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r3)) (__re_nary_intro r3))) Term._at__at_result_null rev)) (Term.Apply Term.str_to_re (Term.String ""))) (__eo_ite (__eo_is_eq (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r2 Term._at__at_result_null rev) (Term.Boolean false)) (__eo_ite (__eo_eq (Term.Apply (Term.Apply Term.str_concat s1) s2) (__str_membership_str (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r3)) (__re_nary_intro r3))) Term._at__at_result_null rev))) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r3)) r2)) (__str_re_consume_rec (__str_membership_str (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r3)) (__re_nary_intro r3))) Term._at__at_result_null rev)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r3)) r2) Term._at__at_result_null rev)) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r3)) r2))) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r3)) r2))))
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.re_concat r1) r2), Term._at__at_result_null, rev => (__eo_ite (__eo_is_eq (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r1 Term._at__at_result_null rev) (Term.Boolean false)) (Term.Boolean false) (__eo_ite (__eo_is_eq (__str_membership_re (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r1 Term._at__at_result_null rev)) (Term.Apply Term.str_to_re (Term.String ""))) (__str_re_consume_rec (__str_membership_str (__str_re_consume_rec (Term.Apply (Term.Apply Term.str_concat s1) s2) r1 Term._at__at_result_null rev)) r2 Term._at__at_result_null rev) (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.re_concat r1) r2))))
  | s1, (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.String ""))) r2), Term._at__at_result_null, rev => (__str_re_consume_rec s1 r2 Term._at__at_result_null rev)
  | s1, (Term.Apply (Term.Apply Term.re_inter r1) r2), b, rev => (__eo_ite (__eo_eq (__str_re_consume_rec s1 (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r1)) (__re_nary_intro r1))) Term._at__at_result_null rev) (Term.Boolean false)) (Term.Boolean false) (__str_re_consume_rec s1 r2 (__result_combine (__str_re_consume_rec s1 (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r1)) (__re_nary_intro r1))) Term._at__at_result_null rev) b) rev))
  | s1, Term.re_all, Term._at__at_result_null, rev => (Term.Apply (Term.Apply Term.str_in_re (Term.String "")) (Term.Apply Term.str_to_re (Term.String "")))
  | s1, Term.re_all, b, rev => b
  | s1, (Term.Apply (Term.Apply Term.re_union r1) r2), b, rev => (__eo_ite (__eo_eq (__str_re_consume_rec s1 (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r1)) (__re_nary_intro r1))) Term._at__at_result_null rev) (Term.Boolean false)) (__str_re_consume_rec s1 r2 b rev) (__str_re_consume_rec s1 r2 (__result_combine (__str_re_consume_rec s1 (__re_str_to_flat_form rev (__eo_ite rev (__eo_list_rev Term.re_concat (__re_nary_intro r1)) (__re_nary_intro r1))) Term._at__at_result_null rev) b) rev))
  | s1, Term.re_none, Term._at__at_result_null, rev => (Term.Boolean false)
  | s1, Term.re_none, b, rev => b
  | s1, r1, Term._at__at_result_null, rev => (Term.Apply (Term.Apply Term.str_in_re s1) r1)
  | _, _, _, _ => Term.Stuck


partial def __str_re_consume : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s, (Term.Apply Term.re_mult r) => (__eo_ite (__eo_eq (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true)) (Term.Boolean false)) (Term.Boolean false) (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)) (Term.Boolean false)) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__str_nary_elim (__str_collect (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))) (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))))) (Term.Boolean false)) (Term.Boolean false) (__eo_requires (__str_membership_re (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true)) (Term.Boolean false)) (Term.Boolean false) (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)) (Term.Boolean false)) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__str_nary_elim (__str_collect (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))) (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false))))))))) (Term.Apply Term.str_to_re (Term.String "")) (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__str_membership_str (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true)) (Term.Boolean false)) (Term.Boolean false) (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)) (Term.Boolean false)) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__str_nary_elim (__str_collect (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))) (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))))))) (Term.Apply Term.re_mult r))))
  | s, r => (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true)) (Term.Boolean false)) (Term.Boolean false) (__eo_ite (__eo_eq (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)) (Term.Boolean false)) (Term.Boolean false) (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__str_nary_elim (__str_collect (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false)))))) (__re_nary_elim (__re_str_from_flat_form (Term.Boolean false) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro (__eo_ite (__eo_and (Term.Boolean false) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))) (Term.Apply Term.str_to_re (Term.String ""))))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro s))) (__re_str_to_flat_form (Term.Boolean true) (__eo_list_rev Term.re_concat (__re_nary_intro r))) Term._at__at_result_null (Term.Boolean true))))))) Term._at__at_result_null (Term.Boolean false))))))))


partial def __eo_l_1___str_is_compatible : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat c1) xs1), (Term.Apply (Term.Apply Term.str_concat c2) xs2) => (__eo_requires (__eo_ite (__eo_eq c1 c2) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons c1) (Term.Apply (Term.Apply Term.__eo_List_cons c2) Term.__eo_List_nil)) (__eo_typeof c1))) (Term.Boolean true) (Term.Boolean false))
  | c1, c2 => (__eo_or (__str_is_empty c1) (__str_is_empty c2))


partial def __str_is_compatible : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat c1) xs1), (Term.Apply (Term.Apply Term.str_concat __eo_lv_c1_2) xs2) => (__eo_ite (__eo_eq c1 __eo_lv_c1_2) (__str_is_compatible xs1 xs2) (__eo_l_1___str_is_compatible (Term.Apply (Term.Apply Term.str_concat c1) xs1) (Term.Apply (Term.Apply Term.str_concat __eo_lv_c1_2) xs2)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___str_is_compatible __eo_dv_1 __eo_dv_2)


partial def __str_overlap_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s) s1), t => (__eo_ite (__str_is_compatible (Term.Apply (Term.Apply Term.str_concat s) s1) t) (Term.Numeral 0) (__eo_add (Term.Numeral 1) (__str_overlap_rec s1 t)))
  | s, t => (Term.Numeral 0)


partial def __str_from_int_eval_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | n, s => (__eo_ite (__eo_eq n (Term.Numeral 0)) (__eo_ite (__eo_eq s (Term.String "")) (Term.String "0") s) (__str_from_int_eval_rec (__eo_zdiv n (Term.Numeral 10)) (__eo_concat (__eo_to_str (__eo_add (Term.Numeral 48) (__eo_zmod n (Term.Numeral 10)))) s)))


partial def __str_to_int_eval_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), e, n => (__eo_ite (__eo_and (__eo_gt (Term.Numeral 10) (__eo_add (__eo_to_z s1) (Term.Numeral (-48 : eo_lit_Int)))) (__eo_not (__eo_is_neg (__eo_add (__eo_to_z s1) (Term.Numeral (-48 : eo_lit_Int)))))) (__str_to_int_eval_rec s2 (__eo_mul e (Term.Numeral 10)) (__eo_add (__eo_mul (__eo_add (__eo_to_z s1) (Term.Numeral (-48 : eo_lit_Int))) e) n)) (Term.Numeral (-1 : eo_lit_Int)))
  | (Term.String ""), e, n => n
  | _, _, _ => Term.Stuck


partial def __str_case_conv_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Boolean true) => (__eo_concat (__eo_to_str (__eo_add (__eo_to_z s1) (__eo_ite (__eo_and (__eo_gt (Term.Numeral 91) (__eo_to_z s1)) (__eo_gt (__eo_to_z s1) (Term.Numeral 64))) (Term.Numeral 32) (Term.Numeral 0)))) (__str_case_conv_rec s2 (Term.Boolean true)))
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Boolean false) => (__eo_concat (__eo_to_str (__eo_add (__eo_to_z s1) (__eo_ite (__eo_and (__eo_gt (Term.Numeral 123) (__eo_to_z s1)) (__eo_gt (__eo_to_z s1) (Term.Numeral 96))) (Term.Numeral (-32 : eo_lit_Int)) (Term.Numeral 0)))) (__str_case_conv_rec s2 (Term.Boolean false)))
  | (Term.String ""), isLower => (Term.String "")
  | _, _ => Term.Stuck


partial def __str_leq_eval_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s1) s2), (Term.Apply (Term.Apply Term.str_concat t1) t2) => (__eo_ite (__eo_eq s1 t1) (__str_leq_eval_rec s2 t2) (__eo_gt (__eo_to_z t1) (__eo_to_z s1)))
  | (Term.String ""), t1 => (Term.Boolean true)
  | s1, t1 => (Term.Boolean false)


partial def __str_eval_replace_all_rec : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, t, u, (Term.Numeral (-1 : eo_lit_Int)), lent => s
  | s, t, u, n, lent => (__eo_concat (__eo_concat (__eo_extract s (Term.Numeral 0) (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))) u) (__str_eval_replace_all_rec (__eo_extract s (__eo_add n lent) (__eo_len s)) t u (__eo_find (__eo_extract s (__eo_add n lent) (__eo_len s)) t) lent))


partial def __eo_prog_string_length_pos : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s => (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq s) (__seq_empty (__eo_typeof s)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len s)) (Term.Numeral 0))) (Term.Boolean false)))


partial def __eo_prog_string_length_non_empty : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq s) t))) => (__eo_requires (__str_is_empty t) (Term.Boolean true) (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Numeral 0))))
  | _ => Term.Stuck


partial def __eo_prog_concat_eq : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq s) t)) => (__eo_mk_apply (__eo_mk_apply Term.eq (__str_nary_elim (__eo_ite rev (__eo_list_rev Term.str_concat (__pair_first (__str_strip_prefix (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t))))) (__pair_first (__str_strip_prefix (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t))))))) (__str_nary_elim (__eo_ite rev (__eo_list_rev Term.str_concat (__pair_second (__str_strip_prefix (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t))))) (__pair_second (__str_strip_prefix (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)))))))
  | _, _ => Term.Stuck


partial def __eo_prog_concat_unify : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq s) t)), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s1)) (Term.Apply Term.str_len t1))) => (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) s1 (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) t1 (Term.Apply (Term.Apply Term.eq s1) t1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_concat_csplit : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq t) s)), (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len u)) (Term.Numeral 0)))) => (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) u (__eo_requires (__eo_is_eq (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral 1)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq u) (__eo_ite rev (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr u) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len u)) (Term.Numeral 1))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr u) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len u)) (Term.Numeral 1)))))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr u) (Term.Numeral 1)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len u)) (Term.Numeral 1))))) (__eo_nil Term.str_concat (__eo_typeof (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))))))))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_concat_split : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq t) s)), (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len tc)) (Term.Apply Term.str_len sc)))) => (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) tc (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) sc (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0))) (__eo_ite rev (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev)))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_nil Term.str_concat (__eo_typeof (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))))))))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_ite rev (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev)))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_nil Term.str_concat (__eo_typeof (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0))))))))) (Term.Boolean false)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.eq (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__seq_empty (__eo_typeof (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.gt (__eo_mk_apply Term.str_len (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev)))) (Term.Numeral 0))) (Term.Boolean true))))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_concat_lprop : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq t) s)), (Proof.pf (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len tc)) (Term.Apply Term.str_len sc))) => (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) tc (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) sc (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0))) (__eo_ite rev (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev)))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__eo_nil Term.str_concat (__eo_typeof (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.eq (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))) (__seq_empty (__eo_typeof (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev))))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.gt (__eo_mk_apply Term.str_len (Term._at_purify (__str_unify_split (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) rev)))) (Term.Numeral 0))) (Term.Boolean true))))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_concat_cprop : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply (Term.Apply Term.eq t) s)), (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len tc)) (Term.Numeral 0)))) => (__eo_requires (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 0)) tc (__eo_mk_apply (Term.Apply Term.eq tc) (__eo_ite rev (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr tc) (Term.Numeral 0)) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len tc)) (__eo_mk_apply Term.str_len (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.neg (__eo_mk_apply Term.str_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.neg (__eo_mk_apply Term.str_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr tc) (Term.Numeral 0)) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len tc)) (__eo_mk_apply Term.str_len (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.neg (__eo_mk_apply Term.str_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1)))))))))))))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral 0)) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))) (__eo_mk_apply (__eo_mk_apply Term.str_concat (Term._at_purify (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.str_substr tc) (__eo_mk_apply Term.str_len (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral 0)) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1)))))))))) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len tc)) (__eo_mk_apply Term.str_len (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral 0)) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))))))))))) (__eo_nil Term.str_concat (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral 0)) (__eo_add (Term.Numeral 1) (__str_overlap_rec (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__str_flatten (__str_nary_intro (__eo_ite rev (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 0) (__eo_add (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0))) (Term.Numeral (-2 : eo_lit_Int)))) (__eo_extract (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)) (Term.Numeral 1) (__eo_len (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro s)) (__str_nary_intro s)) (Term.Numeral 0)))))))) (__eo_ite rev (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1))))) (__str_flatten (__str_nary_intro (__eo_list_nth Term.str_concat (__eo_ite rev (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__str_nary_intro t)) (Term.Numeral 1)))))))))))))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_string_decompose : Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | b, (Proof.pf (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len s)) __eo_lv_n_2)) => (__eo_requires (__eo_eq n __eo_lv_n_2) (Term.Boolean true) (__eo_ite b (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq s) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n)))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n)) n))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n))))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n)) n)))) n)) (Term.Boolean true))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq s) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) n))) (__eo_mk_apply (Term.Apply Term.str_concat (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) n)))) (__eo_nil Term.str_concat (__eo_typeof (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) n)))))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term._at_purify (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) n)))) n)) (Term.Boolean true)))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_exists_string_length : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq U), n, id => (__eo_requires (__eo_gt n (Term.Numeral (-1 : eo_lit_Int))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term._at_witness_string_length (Term.Apply Term.Seq U)) n) id))) n))
  | _, _, _ => Term.Stuck


partial def __eo_prog_string_code_inj : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_code t)) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_code t)) (Term.Apply Term.str_to_code s)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq t) s)) (Term.Boolean false))))


partial def __eo_prog_string_seq_unit_inj : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.seq_unit a)) (Term.Apply Term.seq_unit b))) => (Term.Apply (Term.Apply Term.eq a) b)
  | _ => Term.Stuck


partial def __eo_prog_re_inter : Proof -> Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.str_in_re x) s)), (Proof.pf (Term.Apply (Term.Apply Term.str_in_re __eo_lv_x_2) t)) => (__eo_requires (__eo_eq x __eo_lv_x_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.str_in_re x) (Term.Apply (Term.Apply Term.re_inter s) (Term.Apply (Term.Apply Term.re_inter t) Term.re_all))))
  | _, _ => Term.Stuck


partial def __mk_re_concat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_in_re s) r)) Es), (Term.Apply (Term.Apply Term.str_in_re s1) r1) => (__mk_re_concat Es (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__eo_cons Term.str_concat s s1)) (__eo_cons Term.re_concat r r1)))
  | (Term.Boolean true), (Term.Apply (Term.Apply Term.str_in_re s1) r1) => (Term.Apply (Term.Apply Term.str_in_re s1) r1)
  | _, _ => Term.Stuck


partial def __eo_prog_re_concat : Proof -> Term
  | (Proof.pf E) => (__mk_re_concat (__eo_list_rev Term.and E) (Term.Apply (Term.Apply Term.str_in_re (Term.String "")) (Term.Apply Term.str_to_re (Term.String ""))))
  | _ => Term.Stuck


partial def __mk_re_unfold_pos_star : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, r, (Term.Apply (Term.Apply Term._at__at_pair (Term.Apply (Term.Apply Term.str_concat k1) (Term.Apply (Term.Apply Term.str_concat k2) (Term.Apply (Term.Apply Term.str_concat k3) (Term.String ""))))) M) => (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq t) (Term.String ""))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_in_re t) r)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t) (Term.Apply (Term.Apply Term.str_concat k1) (Term.Apply (Term.Apply Term.str_concat k2) (Term.Apply (Term.Apply Term.str_concat k3) (Term.String "")))))) M)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq k1) (Term.String "")))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq k3) (Term.String "")))) (Term.Boolean true))))) (Term.Boolean false))))
  | _, _, _ => Term.Stuck


partial def __mk_re_unfold_pos : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply Term.re_mult r1) => (__mk_re_unfold_pos_star t r1 (__re_unfold_pos_concat_rec t (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply Term.str_to_re (Term.String ""))))) (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply Term.str_to_re (Term.String ""))))) (Term.Numeral 0)))
  | t, (Term.Apply (Term.Apply Term.re_concat r1) r2) => (__eo_ite (__eo_eq (__pair_second (__re_unfold_pos_concat_rec t (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Numeral 0))) (Term.Boolean true)) (__eo_mk_apply (Term.Apply Term.eq t) (__pair_first (__re_unfold_pos_concat_rec t (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Numeral 0)))) (__eo_cons Term.and (__eo_mk_apply (Term.Apply Term.eq t) (__pair_first (__re_unfold_pos_concat_rec t (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Numeral 0)))) (__pair_second (__re_unfold_pos_concat_rec t (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Apply (Term.Apply Term.re_concat r1) r2) (Term.Numeral 0)))))
  | _, _ => Term.Stuck


partial def __eo_prog_re_unfold_pos : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.str_in_re t) r)) => (__mk_re_unfold_pos t r)
  | _ => Term.Stuck


partial def __mk_re_unfold_neg_concat_fixed : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s, (Term.Apply (Term.Apply Term.re_concat r1) r2), rev => (__eo_ite rev (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.str_substr s) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (__str_fixed_len_re r1))) (__str_fixed_len_re r1))) r1))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (__str_fixed_len_re r1)))) (__eo_list_singleton_elim Term.re_concat (__eo_ite rev (__eo_list_rev Term.re_concat r2) r2))))) (Term.Boolean false))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__eo_mk_apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) (__str_fixed_len_re r1))) r1))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.str_in_re (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.str_substr s) (__str_fixed_len_re r1)) (__eo_mk_apply (Term.Apply Term.neg (Term.Apply Term.str_len s)) (__str_fixed_len_re r1)))) (__eo_list_singleton_elim Term.re_concat r2)))) (Term.Boolean false))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_re_unfold_neg_concat_fixed : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | rev, (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re s) r))) => (__mk_re_unfold_neg_concat_fixed s (__eo_ite rev (__eo_list_rev Term.re_concat r) r) rev)
  | _, _ => Term.Stuck


partial def __mk_re_unfold_neg : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, (Term.Apply Term.re_mult r1) => (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t) (Term.String "")))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.leq (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.lt (Term.Apply Term.str_len t)) (Term.Var "@var.str_index" Term.Int))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0)) (Term.Var "@var.str_index" Term.Int))) r1))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t)) (Term.Var "@var.str_index" Term.Int)))) (Term.Apply Term.re_mult r1)))) (Term.Boolean false))))))) (Term.Boolean true)))
  | t, (Term.Apply (Term.Apply Term.re_concat r1) r2) => (__eo_mk_apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.str_index" Term.Int)) Term.__eo_List_nil)) (__eo_mk_apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.lt (Term.Var "@var.str_index" Term.Int)) (Term.Numeral 0))) (__eo_mk_apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.lt (Term.Apply Term.str_len t)) (Term.Var "@var.str_index" Term.Int))) (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Numeral 0)) (Term.Var "@var.str_index" Term.Int))) r1))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_mk_apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) (Term.Var "@var.str_index" Term.Int)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t)) (Term.Var "@var.str_index" Term.Int)))) (__eo_list_singleton_elim Term.re_concat r2)))) (Term.Boolean false))))))
  | _, _ => Term.Stuck


partial def __eo_prog_re_unfold_neg : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re t) r))) => (__mk_re_unfold_neg t r)
  | _ => Term.Stuck


partial def __str_mk_ext_deq : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, t, k, (Term.Apply Term.Seq Term.Char) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) k) (Term.Numeral 1))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) k) (Term.Numeral 1))))
  | s, t, k, (Term.Apply Term.Seq T) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.seq_nth s) k)) (Term.Apply (Term.Apply Term.seq_nth t) k)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_string_ext : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq s) t))) => (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) (Term.Apply Term.str_len t)))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (__eo_mk_apply Term.and (__str_mk_ext_deq s t (Term.Apply (Term.Apply Term._at_strings_deq_diff s) t) (__eo_typeof s))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_strings_deq_diff s) t))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term._at_strings_deq_diff s) t)) (Term.Apply Term.str_len s))) (Term.Boolean true))))) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_string_reduction : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s => (__eo_mk_apply (__eo_mk_apply Term.and (__str_reduction_pred s)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq s) (Term._at_purify s))) (Term.Boolean true)))


partial def __eo_prog_string_eager_reduction : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s => (__mk_str_eager_reduction s)


partial def __eo_prog_arith_string_pred_entail : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Boolean true)) => (__eo_requires (__str_arith_entail_simple n) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Boolean true)))
  | _ => Term.Stuck


partial def __eo_prog_arith_string_pred_safe_approx : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.geq m) (Term.Numeral 0))) => (__eo_requires (__str_arith_entail_is_approx n m (Term.Boolean true)) (Term.Boolean true) (__eo_requires (__str_arith_entail_simple_pred (Term.Apply (Term.Apply Term.geq m) (Term.Numeral 0))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.geq m) (Term.Numeral 0)))))
  | _ => Term.Stuck


partial def __eo_prog_str_in_re_eval : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b) => (__eo_requires (__str_eval_str_in_re s r) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b))
  | _ => Term.Stuck


partial def __eo_prog_str_in_re_consume : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b) => (__eo_requires (__str_re_consume s r) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b))
  | _ => Term.Stuck


partial def __eo_prog_re_loop_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.re_loop l) u) r1)) r2) => (__eo_requires (__eo_is_neg (__eo_add (__eo_neg l) u)) (Term.Boolean false) (__eo_requires (__eo_list_singleton_elim Term.re_union (__str_mk_re_loop_elim_rec l (__eo_add (__eo_neg l) u) r1 (Term.Apply Term.str_to_re (Term.String "")))) r2 (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.re_loop l) u) r1)) r2)))
  | _ => Term.Stuck


partial def __eo_prog_re_eq_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq r1) r2)) Q) => (__eo_requires Q (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var "@var.re_eq" (Term.Apply Term.Seq Term.Char))) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.Var "@var.re_eq" (Term.Apply Term.Seq Term.Char))) r1)) (Term.Apply (Term.Apply Term.str_in_re (Term.Var "@var.re_eq" (Term.Apply Term.Seq Term.Char))) r2))) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq r1) r2)) Q))
  | _ => Term.Stuck


partial def __eo_prog_re_inter_inclusion : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_inter r1) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp r2)) Term.re_all))) Term.re_none) => (__eo_requires (__str_re_includes r2 r1) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_inter r1) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp r2)) Term.re_all))) Term.re_none))
  | _ => Term.Stuck


partial def __eo_prog_re_union_inclusion : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_union r1) (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.re_comp r2)) Term.re_none))) (Term.Apply Term.re_mult Term.re_allchar)) => (__eo_requires (__str_re_includes r1 r2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_union r1) (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.re_comp r2)) Term.re_none))) (Term.Apply Term.re_mult Term.re_allchar)))
  | _ => Term.Stuck


partial def __eo_prog_str_in_re_concat_star_char : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply Term.re_mult r))) b) => (__eo_requires (__str_fixed_len_re r) (Term.Numeral 1) (__eo_requires (__str_mk_str_in_re_concat_star_char (Term.Apply (Term.Apply Term.str_concat s1) s2) (Term.Apply Term.re_mult r)) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply Term.re_mult r))) b)))
  | _ => Term.Stuck


partial def __eo_prog_str_in_re_sigma : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b) => (__eo_requires (__str_mk_str_in_re_sigma_rec s r (Term.Numeral 0) (Term.Boolean true)) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) r)) b))
  | _ => Term.Stuck


partial def __eo_prog_str_in_re_sigma_star : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) (Term.Apply Term.re_mult r))) b) => (__eo_requires (__str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0)) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s) (Term.Apply Term.re_mult r))) b))
  | _ => Term.Stuck


partial def __str_multiset_overapprox : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s) ss) => (__eo_list_concat Term.__eo_List_cons (__str_multiset_overapprox s) (__str_multiset_overapprox ss))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m) => (__str_multiset_overapprox s)
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace s) t) r) => (__eo_list_concat Term.__eo_List_cons (__str_multiset_overapprox s) (__str_multiset_overapprox r))
  | s => (__eo_ite (__str_is_empty s) Term.__eo_List_nil (__eo_ite (__eo_is_str s) (__eo_ite (__eo_gt (__eo_len s) (Term.Numeral 1)) (__str_multiset_overapprox (__str_flatten_word s)) (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil)) (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil)))


partial def __str_is_multiset_subset_strict : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat s) ss), xs, nr => (__str_is_multiset_subset_strict ss (__eo_list_erase Term.__eo_List_cons xs s) (__eo_ite (__eo_eq xs (__eo_list_erase Term.__eo_List_cons xs s)) (Term.Apply (Term.Apply Term.__eo_List_cons s) nr) nr))
  | emp, xs, (Term.Apply (Term.Apply Term.__eo_List_cons s) nr) => (__eo_ite (__are_distinct_terms_list_rec s xs (__eo_typeof s)) (Term.Boolean true) (__str_is_multiset_subset_strict emp xs nr))
  | emp, xs, nr => (Term.Boolean false)


partial def __eo_prog_str_ctn_multiset_subset : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains t) s)) (Term.Boolean false)) => (__eo_requires (__str_is_multiset_subset_strict (__str_flatten (__str_nary_intro s)) (__str_multiset_overapprox t) Term.__eo_List_nil) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains t) s)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_str_overlap_split_ctn : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat c) (Term.Apply (Term.Apply Term.str_concat s) emp)))) d)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains __eo_lv_t_2) __eo_lv_d_2)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains __eo_lv_s_2) __eo_lv_d_3)) (Term.Boolean false)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq t __eo_lv_t_2) (__eo_eq d __eo_lv_d_2)) (__eo_eq s __eo_lv_s_2)) (__eo_eq d __eo_lv_d_3)) (Term.Boolean true) (__eo_requires (__str_is_empty emp) (Term.Boolean true) (__eo_requires (__eo_gt (__str_value_len c) (__str_overlap_rec (__str_flatten (__str_nary_intro c)) (__str_flatten (__str_nary_intro d)))) (Term.Boolean false) (__eo_requires (__eo_gt (__str_value_len d) (__str_overlap_rec (__str_flatten (__str_nary_intro d)) (__str_flatten (__str_nary_intro c)))) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat c) (Term.Apply (Term.Apply Term.str_concat s) emp)))) d)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains t) d)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains s) d)) (Term.Boolean false))))))))
  | _ => Term.Stuck


partial def __eo_prog_str_overlap_endpoints_ctn : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply Term.str_concat c1) (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c2) emp)))) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) __eo_lv_emp_2))))) (Term.Apply (Term.Apply Term.str_contains __eo_lv_s_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_d1_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_d2_2) __eo_lv_emp_3))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq emp __eo_lv_emp_2) (__eo_eq s __eo_lv_s_2)) (__eo_eq d1 __eo_lv_d1_2)) (__eo_eq t __eo_lv_t_2)) (__eo_eq d2 __eo_lv_d2_2)) (__eo_eq emp __eo_lv_emp_3)) (Term.Boolean true) (__eo_requires (__str_is_empty emp) (Term.Boolean true) (__eo_requires (__eo_gt (__str_value_len c1) (__str_overlap_rec (__str_flatten (__str_nary_intro c1)) (__str_flatten (__str_nary_intro d1)))) (Term.Boolean false) (__eo_requires (__eo_gt (__str_value_len c2) (__str_overlap_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro c2))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro d2))))) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply Term.str_concat c1) (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c2) emp)))) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) emp))))) (Term.Apply (Term.Apply Term.str_contains s) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) emp)))))))))
  | _ => Term.Stuck


partial def __eo_prog_str_overlap_endpoints_indexof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c) emp))) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d) __eo_lv_emp_2))) (Term.Numeral 0))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_s_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_d_2) __eo_lv_emp_3))) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq emp __eo_lv_emp_2) (__eo_eq s __eo_lv_s_2)) (__eo_eq t __eo_lv_t_2)) (__eo_eq d __eo_lv_d_2)) (__eo_eq emp __eo_lv_emp_3)) (Term.Boolean true) (__eo_requires (__str_is_empty emp) (Term.Boolean true) (__eo_requires (__eo_gt (__str_value_len c) (__str_overlap_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro c))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro d))))) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c) emp))) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d) emp))) (Term.Numeral 0))) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof s) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d) emp))) (Term.Numeral 0))))))
  | _ => Term.Stuck


partial def __eo_prog_str_overlap_endpoints_replace : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply Term.str_concat c1) (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c2) emp)))) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) __eo_lv_emp_2)))) r)) (Term.Apply (Term.Apply Term.str_concat __eo_lv_c1_2) (Term.Apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_replace __eo_lv_s_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_d1_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) (Term.Apply (Term.Apply Term.str_concat __eo_lv_d2_2) __eo_lv_emp_3)))) __eo_lv_r_2)) (Term.Apply (Term.Apply Term.str_concat __eo_lv_c2_2) __eo_lv_emp_4)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq emp __eo_lv_emp_2) (__eo_eq c1 __eo_lv_c1_2)) (__eo_eq s __eo_lv_s_2)) (__eo_eq d1 __eo_lv_d1_2)) (__eo_eq t __eo_lv_t_2)) (__eo_eq d2 __eo_lv_d2_2)) (__eo_eq emp __eo_lv_emp_3)) (__eo_eq r __eo_lv_r_2)) (__eo_eq c2 __eo_lv_c2_2)) (__eo_eq emp __eo_lv_emp_4)) (Term.Boolean true) (__eo_requires (__str_is_empty emp) (Term.Boolean true) (__eo_requires (__eo_gt (__str_value_len c1) (__str_overlap_rec (__str_flatten (__str_nary_intro c1)) (__str_flatten (__str_nary_intro d1)))) (Term.Boolean false) (__eo_requires (__eo_gt (__str_value_len c2) (__str_overlap_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro c2))) (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro d2))))) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply Term.str_concat c1) (Term.Apply (Term.Apply Term.str_concat s) (Term.Apply (Term.Apply Term.str_concat c2) emp)))) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) emp)))) r)) (Term.Apply (Term.Apply Term.str_concat c1) (Term.Apply (Term.Apply Term.str_concat (Term.Apply (Term.Apply (Term.Apply Term.str_replace s) (Term.Apply (Term.Apply Term.str_concat d1) (Term.Apply (Term.Apply Term.str_concat t) (Term.Apply (Term.Apply Term.str_concat d2) emp)))) r)) (Term.Apply (Term.Apply Term.str_concat c2) emp))))))))
  | _ => Term.Stuck


partial def __eo_prog_str_indexof_re_eval : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) m) => (__eo_requires (__eo_ite (__eo_or (__eo_gt n (__eo_len s)) (__eo_is_neg n)) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_eq (__pair_first (__eo_requires (__eo_is_str (__eo_extract s n (__eo_len s))) (Term.Boolean true) (__str_first_match_rec (__eo_extract s n (__eo_len s)) r (Term.Apply (Term.Apply Term.re_concat r) (Term.Apply (Term.Apply Term.re_concat Term.re_all) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0) (__eo_len (__eo_extract s n (__eo_len s)))))) (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int)) (__eo_add n (__pair_first (__eo_requires (__eo_is_str (__eo_extract s n (__eo_len s))) (Term.Boolean true) (__str_first_match_rec (__eo_extract s n (__eo_len s)) r (Term.Apply (Term.Apply Term.re_concat r) (Term.Apply (Term.Apply Term.re_concat Term.re_all) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0) (__eo_len (__eo_extract s n (__eo_len s))))))))) m (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) m))
  | _ => Term.Stuck


partial def __str_eval_replace_re : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, r, t, (Term.Apply (Term.Apply Term._at__at_pair (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) => s
  | s, r, t, (Term.Apply (Term.Apply Term._at__at_pair sp) ep) => (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_extract s (Term.Numeral 0) (__eo_add sp (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply (Term.Apply Term.str_concat t) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_extract s ep (__eo_len s))) (Term.String ""))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_re_eval : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re s) r) t)) u) => (__eo_requires (__str_eval_replace_re s r t (__eo_requires (__eo_is_str s) (Term.Boolean true) (__str_first_match_rec s r (Term.Apply (Term.Apply Term.re_concat r) (Term.Apply (Term.Apply Term.re_concat Term.re_all) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0) (__eo_len s)))) u (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re s) r) t)) u))
  | _ => Term.Stuck


partial def __str_eval_replace_re_all_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | (Term.String ""), r, t, (Term.Apply (Term.Apply Term._at__at_pair (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) => (Term.String "")
  | s, r, t, (Term.Apply (Term.Apply Term._at__at_pair (Term.Numeral (-1 : eo_lit_Int))) (Term.Numeral (-1 : eo_lit_Int))) => (__eo_cons Term.str_concat s (Term.String ""))
  | s, r, t, (Term.Apply (Term.Apply Term._at__at_pair sp) ep) => (__eo_cons Term.str_concat (__eo_extract s (Term.Numeral 0) (__eo_add sp (Term.Numeral (-1 : eo_lit_Int)))) (__eo_cons Term.str_concat t (__str_eval_replace_re_all_rec (__eo_extract s ep (__eo_len s)) r t (__eo_requires (__eo_is_str (__eo_extract s ep (__eo_len s))) (Term.Boolean true) (__str_first_match_rec (__eo_extract s ep (__eo_len s)) r (Term.Apply (Term.Apply Term.re_concat r) (Term.Apply (Term.Apply Term.re_concat Term.re_all) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0) (__eo_len (__eo_extract s ep (__eo_len s))))))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_re_all_eval : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) u) => (__eo_requires (__eo_list_singleton_elim Term.str_concat (__str_eval_replace_re_all_rec s (Term.Apply (Term.Apply Term.re_inter r) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp (Term.Apply Term.str_to_re (Term.String "")))) Term.re_all)) t (__eo_requires (__eo_is_str s) (Term.Boolean true) (__str_first_match_rec s (Term.Apply (Term.Apply Term.re_inter r) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp (Term.Apply Term.str_to_re (Term.String "")))) Term.re_all)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply (Term.Apply Term.re_inter r) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp (Term.Apply Term.str_to_re (Term.String "")))) Term.re_all))) (Term.Apply (Term.Apply Term.re_concat Term.re_all) (Term.Apply Term.str_to_re (Term.String "")))) (Term.Numeral 0) (__eo_len s))))) u (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all s) r) t)) u))
  | _ => Term.Stuck


partial def __eo_l_2___seq_is_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit et)) ts), (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit es)) ss) => (__eo_requires (__eo_ite (__eo_eq et es) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons et) (Term.Apply (Term.Apply Term.__eo_List_cons es) Term.__eo_List_nil)) (__eo_typeof et))) (Term.Boolean true) (Term.Boolean false))
  | (Term.seq_empty (Term.Apply Term.Seq T)), t => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit et)) ts), (Term.seq_empty (Term.Apply Term.Seq T)) => (Term.Boolean false)
  | _, _ => Term.Stuck


partial def __eo_l_1___seq_is_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.str_concat t) ts), (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) ss) => (__eo_ite (__eo_eq t __eo_lv_t_2) (__seq_is_prefix ts ss) (__eo_l_2___seq_is_prefix (Term.Apply (Term.Apply Term.str_concat t) ts) (Term.Apply (Term.Apply Term.str_concat __eo_lv_t_2) ss)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_2___seq_is_prefix __eo_dv_1 __eo_dv_2)


partial def __seq_is_prefix : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, __eo_lv_t_2 => (__eo_ite (__eo_eq t __eo_lv_t_2) (Term.Boolean true) (__eo_l_1___seq_is_prefix t __eo_lv_t_2))


partial def __eo_l_1___seq_find : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.seq_empty (Term.Apply Term.Seq T)), s, n => (Term.Numeral (-1 : eo_lit_Int))
  | (Term.Apply (Term.Apply Term.str_concat t) ts), s, n => (__eo_ite (__seq_is_prefix (Term.Apply (Term.Apply Term.str_concat t) ts) s) n (__seq_find ts s (__eo_add n (Term.Numeral 1))))
  | _, _, _ => Term.Stuck


partial def __seq_find : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, __eo_lv_t_2, n => (__eo_ite (__eo_eq t __eo_lv_t_2) n (__eo_l_1___seq_find t __eo_lv_t_2 n))


partial def __seq_subsequence : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | l, u, (Term.seq_empty (Term.Apply Term.Seq T)) => (Term.seq_empty (Term.Apply Term.Seq T))
  | l, (Term.Numeral 0), t => (Term.seq_empty (__eo_typeof t))
  | (Term.Numeral 0), u, (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e)) ts) => (__eo_cons Term.str_concat (Term.Apply Term.seq_unit e) (__seq_subsequence (Term.Numeral 0) (__eo_add u (Term.Numeral (-1 : eo_lit_Int))) ts))
  | l, u, (Term.Apply (Term.Apply Term.str_concat (Term.Apply Term.seq_unit e)) ts) => (__seq_subsequence (__eo_add l (Term.Numeral (-1 : eo_lit_Int))) (__eo_add u (Term.Numeral (-1 : eo_lit_Int))) ts)
  | _, _, _ => Term.Stuck


partial def __seq_eval_replace_all_rec : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | s, t, u, (Term.Numeral (-1 : eo_lit_Int)), lent => s
  | s, t, u, n, lent => (__eo_list_concat Term.str_concat (__seq_subsequence (Term.Numeral 0) n s) (__eo_list_concat Term.str_concat u (__seq_eval_replace_all_rec (__seq_subsequence (__eo_add n lent) (__str_value_len s) s) t u (__seq_find (__seq_subsequence (__eo_add n lent) (__str_value_len s) s) t (Term.Numeral 0)) lent)))


partial def __seq_eval : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.seq_nth t) n) => (__seq_element_of_unit (__eo_list_nth Term.str_concat (__str_nary_intro t) n))
  | (Term.Apply Term.str_len t) => (__str_value_len (__str_nary_intro t))
  | (Term.Apply (Term.Apply Term.str_concat t) ts) => (__str_nary_elim (__eo_list_concat Term.str_concat (__str_nary_intro t) (__str_nary_intro (__seq_eval ts))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) n) m) => (__str_nary_elim (__seq_subsequence n (__eo_add n m) (__str_nary_intro t)))
  | (Term.Apply (Term.Apply Term.str_contains t) s) => (__eo_not (__eo_is_neg (__seq_find (__str_nary_intro t) (__str_nary_intro s) (Term.Numeral 0))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace t) s) r) => (__eo_ite (__eo_is_neg (__seq_find (__str_nary_intro t) (__str_nary_intro s) (Term.Numeral 0))) t (__str_nary_elim (__eo_list_concat Term.str_concat (__seq_subsequence (Term.Numeral 0) (__seq_find (__str_nary_intro t) (__str_nary_intro s) (Term.Numeral 0)) (__str_nary_intro t)) (__eo_list_concat Term.str_concat (__str_nary_intro r) (__seq_subsequence (__eo_add (__seq_find (__str_nary_intro t) (__str_nary_intro s) (Term.Numeral 0)) (__str_value_len (__str_nary_intro s))) (__str_value_len (__str_nary_intro t)) (__str_nary_intro t))))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t) s) r) => (__eo_ite (__eo_eq (__str_value_len s) (Term.Numeral 0)) t (__str_nary_elim (__seq_eval_replace_all_rec (__str_nary_intro t) (__str_nary_intro s) (__str_nary_intro r) (__seq_find (__str_nary_intro s) (__str_nary_intro t) (Term.Numeral 0)) (__str_value_len (__str_nary_intro t)))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) s) n) => (__seq_find (__seq_subsequence n (__str_value_len (__str_nary_intro t)) (__str_nary_intro t)) (__str_nary_intro s) n)
  | (Term.Apply (Term.Apply Term.str_prefixof t) s) => (__seq_is_prefix (__str_nary_intro t) (__str_nary_intro s))
  | (Term.Apply (Term.Apply Term.str_suffixof t) s) => (__seq_is_prefix (__eo_list_rev Term.str_concat (__str_nary_intro t)) (__eo_list_rev Term.str_concat (__str_nary_intro s)))
  | (Term.Apply (Term.Apply Term.str_at t) n) => (__seq_eval (Term.Apply (Term.Apply (Term.Apply Term.str_substr t) n) (Term.Numeral 1)))
  | (Term.Apply Term.str_rev t) => (__str_nary_elim (__eo_list_rev Term.str_concat (__str_nary_intro t)))
  | t => t


partial def __eo_prog_seq_eval_op : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t) u) => (__eo_requires (__seq_eval t) u (Term.Apply (Term.Apply Term.eq t) u))
  | _ => Term.Stuck


partial def __eo_prog_sets_singleton_inj : Proof -> Term
  | (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.set_singleton a)) (Term.Apply Term.set_singleton b))) => (Term.Apply (Term.Apply Term.eq a) b)
  | _ => Term.Stuck


partial def __eo_prog_sets_ext : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a) b))) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member (Term._at_sets_deq_diff a b)) a)) (Term.Apply (Term.Apply Term.set_member (Term._at_sets_deq_diff a b)) b)))
  | _ => Term.Stuck


partial def __set_union_to_list : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.set_union (Term.Apply Term.set_singleton e)) t) => (__eo_cons Term.__eo_List_cons e (__set_union_to_list t))
  | (Term.set_empty (Term.Apply Term.Set T)) => Term.__eo_List_nil
  | (Term.Apply Term.set_singleton e) => (Term.Apply (Term.Apply Term.__eo_List_cons e) Term.__eo_List_nil)
  | _ => Term.Stuck


partial def __eval_sets_inter : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons a) as), bs => (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons bs a)) (__eo_requires (__are_distinct_terms_list_rec a bs (__eo_typeof a)) (Term.Boolean true) (__eval_sets_inter as bs)) (__eo_cons Term.__eo_List_cons a (__eval_sets_inter as bs)))
  | Term.__eo_List_nil, bs => Term.__eo_List_nil
  | _, _ => Term.Stuck


partial def __eval_sets_minus : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons a) as), bs => (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons bs a)) (__eo_requires (__are_distinct_terms_list_rec a bs (__eo_typeof a)) (Term.Boolean true) (__eo_cons Term.__eo_List_cons a (__eval_sets_minus as bs))) (__eval_sets_minus as bs))
  | Term.__eo_List_nil, bs => Term.__eo_List_nil
  | _, _ => Term.Stuck


partial def __eval_sets_op : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.set_union s) t) => (__eo_list_concat Term.__eo_List_cons (__set_union_to_list s) (__set_union_to_list t))
  | (Term.Apply (Term.Apply Term.set_inter s) t) => (__eval_sets_inter (__set_union_to_list s) (__set_union_to_list t))
  | (Term.Apply (Term.Apply Term.set_minus s) t) => (__eval_sets_minus (__set_union_to_list s) (__set_union_to_list t))
  | _ => Term.Stuck


partial def __eo_prog_sets_eval_op : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__eo_list_meq Term.__eo_List_cons (__eo_list_setof Term.__eo_List_cons (__eval_sets_op a)) (__set_union_to_list b)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __set_eval_insert : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs), t => (__eo_mk_apply (Term.Apply Term.set_union (Term.Apply Term.set_singleton x)) (__set_eval_insert xs t))
  | Term.__eo_List_nil, t => t
  | _, _ => Term.Stuck


partial def __eo_prog_sets_insert_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_insert es) s)) t) => (__eo_requires (__set_eval_insert es s) t (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_insert es) s)) t))
  | _ => Term.Stuck


partial def __eo_l_1___abconv_ubv_to_int_elim : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | b, i, w, p => (__eo_cons Term.plus (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract i) i) b)) (Term.Binary 1 1))) p) (Term.Numeral 0)) (__abconv_ubv_to_int_elim b (__eo_add i (Term.Numeral 1)) w (__eo_mul p (Term.Numeral 2))))


partial def __abconv_ubv_to_int_elim : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | b, w, __eo_lv_w_2, p => (__eo_ite (__eo_eq w __eo_lv_w_2) (Term.Numeral 0) (__eo_l_1___abconv_ubv_to_int_elim b w __eo_lv_w_2 p))


partial def __eo_prog_ubv_to_int_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply Term.ubv_to_int b)) m) => (__eo_requires (__eo_list_singleton_elim Term.plus (__abconv_ubv_to_int_elim b (Term.Numeral 0) (__bv_bitwidth (__eo_typeof b)) (Term.Numeral 1))) m (Term.Apply (Term.Apply Term.eq (Term.Apply Term.ubv_to_int b)) m))
  | _ => Term.Stuck


partial def __abconv_int_to_bv_elim : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | n, (Term.Numeral 0), p => (Term.Binary 0 0)
  | n, w, p => (__eo_cons Term.concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.ite (__eo_mk_apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.mod_total n) p)) (__eo_zdiv p (Term.Numeral 2)))) (Term.Binary 1 1)) (Term.Binary 1 0)) (__abconv_int_to_bv_elim n (__eo_add w (Term.Numeral (-1 : eo_lit_Int))) (__eo_zdiv p (Term.Numeral 2))))


partial def __eo_prog_int_to_bv_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.int_to_bv w) n)) b) => (__eo_requires (__eo_list_singleton_elim Term.concat (__abconv_int_to_bv_elim n w (__eo_ite (__eo_is_z w) (__eo_ite (__eo_is_neg w) (Term.Numeral 0) (__arith_eval_int_pow_2_rec w)) (Term.Apply Term.int_pow2 w)))) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.int_to_bv w) n)) b))
  | _ => Term.Stuck


partial def __eo_prog_instantiate : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | ts, (Proof.pf (Term.Apply (Term.Apply Term.forall xs) F)) => (__substitute_simul F xs ts)
  | _, _ => Term.Stuck


partial def __mk_skolems : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs), F, i => (__eo_cons Term.__eo_List_cons (Term._at_quantifiers_skolemize F i) (__mk_skolems xs F (__eo_add i (Term.Numeral 1))))
  | Term.__eo_List_nil, F, i => Term.__eo_List_nil
  | _, _, _ => Term.Stuck


partial def __eo_prog_skolemize : Proof -> Term
  | (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall x) G))) => (__substitute_simul (Term.Apply Term.not G) x (__mk_skolems x (Term.Apply (Term.Apply Term.forall x) G) (Term.Numeral 0)))
  | _ => Term.Stuck


partial def __eo_prog_skolem_intro : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term._at_purify x) => (Term.Apply (Term.Apply Term.eq (Term._at_purify x)) x)
  | _ => Term.Stuck


partial def __eo_prog_alpha_equiv : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t, vs, ts => (__eo_requires (__is_var_list vs) (Term.Boolean true) (__eo_requires (__is_var_list ts) (Term.Boolean true) (__eo_requires (__contains_atomic_term_list_free_rec t vs Term.__eo_List_nil) (Term.Boolean false) (__eo_requires (__contains_atomic_term_list t ts) (Term.Boolean false) (__eo_mk_apply (Term.Apply Term.eq t) (__substitute_simul t vs ts))))))


partial def __eo_prog_beta_reduce : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__beta_reduce a Term.__eo_List_nil) b (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __eo_prog_quant_var_reordering : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) (Term.Apply (Term.Apply Term.forall y) __eo_lv_F_2)) => (__eo_requires (__eo_eq F __eo_lv_F_2) (Term.Boolean true) (__eo_requires (__eo_list_meq Term.__eo_List_cons x y) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) (Term.Apply (Term.Apply Term.forall y) F))))
  | _ => Term.Stuck


partial def __eo_prog_exists_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.exists x) F)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall __eo_lv_x_2) (Term.Apply Term.not __eo_lv_F_2)))) => (__eo_requires (__eo_and (__eo_eq x __eo_lv_x_2) (__eo_eq F __eo_lv_F_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.exists x) F)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.forall x) (Term.Apply Term.not F)))))
  | _ => Term.Stuck


partial def __mk_quant_unused_vars_rec : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List_nil, F => Term.__eo_List_nil
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs), F => (__eo_ite (__contains_atomic_term F x) (__eo_cons Term.__eo_List_cons x (__eo_list_erase Term.__eo_List_cons (__mk_quant_unused_vars_rec xs F) x)) (__mk_quant_unused_vars_rec xs F))
  | _, _ => Term.Stuck


partial def __mk_quant : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Q, Term.__eo_List_nil, F => F
  | Q, x, F => (Term.Apply (Term.Apply Q x) F)


partial def __eo_prog_quant_unused_vars : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Q x) F)) G) => (__eo_requires (__mk_quant Q (__mk_quant_unused_vars_rec x F) F) G (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Q x) F)) G))
  | _ => Term.Stuck


partial def __eo_l_1___mk_quant_merge_prenex : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Q, F, y => (Term.Apply (Term.Apply Q y) F)


partial def __mk_quant_merge_prenex : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Q, (Term.Apply (Term.Apply __eo_lv_Q_2 x) F), y => (__eo_ite (__eo_eq Q __eo_lv_Q_2) (__mk_quant_merge_prenex Q F (__eo_list_concat Term.__eo_List_cons y x)) (__eo_l_1___mk_quant_merge_prenex Q (Term.Apply (Term.Apply __eo_lv_Q_2 x) F) y))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___mk_quant_merge_prenex __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_prog_quant_merge_prenex : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Q x) F)) G) => (__eo_requires (__eo_or (__eo_eq Q Term.forall) (__eo_eq Q Term.exists)) (Term.Boolean true) (__eo_requires (__mk_quant_merge_prenex Q (Term.Apply (Term.Apply Q x) F) Term.__eo_List_nil) G (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Q x) F)) G)))
  | _ => Term.Stuck


partial def __mk_quant_miniscope_and : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.and f) fs) => (__eo_cons Term.and (Term.Apply (Term.Apply Term.forall x) f) (__mk_quant_miniscope_and x fs))
  | x, (Term.Boolean true) => (Term.Boolean true)
  | _, _ => Term.Stuck


partial def __eo_prog_quant_miniscope_and : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) G) => (__eo_requires (__mk_quant_miniscope_and x F) G (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) G))
  | _ => Term.Stuck


partial def __eo_l_3___is_quant_miniscope_or : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List_nil, (Term.Boolean false), (Term.Boolean false) => (Term.Boolean true)
  | x, f, g => (Term.Boolean false)


partial def __eo_l_2___is_quant_miniscope_or : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons x) xs), (Term.Apply (Term.Apply Term.or f) fs), (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_x_2) ys)) __eo_lv_f_2)) gs) => (__eo_ite (__eo_and (__eo_eq x __eo_lv_x_2) (__eo_eq f __eo_lv_f_2)) (__eo_requires (__contains_atomic_term gs x) (Term.Boolean false) (__is_quant_miniscope_or xs (Term.Apply (Term.Apply Term.or f) fs) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.forall ys) f)) gs))) (__eo_l_3___is_quant_miniscope_or (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) (Term.Apply (Term.Apply Term.or f) fs) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_x_2) ys)) __eo_lv_f_2)) gs)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_3___is_quant_miniscope_or __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_1___is_quant_miniscope_or : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.or f) fs), (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.forall Term.__eo_List_nil) __eo_lv_f_2)) gs) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_requires (__contains_atomic_term_list f x) (Term.Boolean false) (__is_quant_miniscope_or x fs gs)) (__eo_l_2___is_quant_miniscope_or x (Term.Apply (Term.Apply Term.or f) fs) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.forall Term.__eo_List_nil) __eo_lv_f_2)) gs)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_2___is_quant_miniscope_or __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __is_quant_miniscope_or : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.or f) fs), (Term.Apply (Term.Apply Term.or __eo_lv_f_2) gs) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_requires (__contains_atomic_term_list f x) (Term.Boolean false) (__is_quant_miniscope_or x fs gs)) (__eo_l_1___is_quant_miniscope_or x (Term.Apply (Term.Apply Term.or f) fs) (Term.Apply (Term.Apply Term.or __eo_lv_f_2) gs)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___is_quant_miniscope_or __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_prog_quant_miniscope_or : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) G) => (__eo_requires (__is_quant_miniscope_or x F G) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) F)) G))
  | _ => Term.Stuck


partial def __eo_prog_quant_miniscope_ite : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) (Term.Apply (Term.Apply (Term.Apply Term.ite A) F1) F2))) (Term.Apply (Term.Apply (Term.Apply Term.ite __eo_lv_A_2) (Term.Apply (Term.Apply Term.forall __eo_lv_x_2) __eo_lv_F1_2)) (Term.Apply (Term.Apply Term.forall __eo_lv_x_3) __eo_lv_F2_2))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq A __eo_lv_A_2) (__eo_eq x __eo_lv_x_2)) (__eo_eq F1 __eo_lv_F1_2)) (__eo_eq x __eo_lv_x_3)) (__eo_eq F2 __eo_lv_F2_2)) (Term.Boolean true) (__eo_requires (__contains_atomic_term_list A x) (Term.Boolean false) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall x) (Term.Apply (Term.Apply (Term.Apply Term.ite A) F1) F2))) (Term.Apply (Term.Apply (Term.Apply Term.ite A) (Term.Apply (Term.Apply Term.forall x) F1)) (Term.Apply (Term.Apply Term.forall x) F2)))))
  | _ => Term.Stuck


partial def __eo_l_1___mk_quant_var_elim_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.or (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_x_2) t))) F) => (__eo_requires (__eo_eq x __eo_lv_x_2) (Term.Boolean true) (__eo_requires (__contains_atomic_term t x) (Term.Boolean false) (__substitute x t (__eo_list_singleton_elim Term.or F))))
  | _, _ => Term.Stuck


partial def __mk_quant_var_elim_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_x_2) t)) => (__eo_ite (__eo_eq x __eo_lv_x_2) (__eo_requires (__contains_atomic_term t x) (Term.Boolean false) (__substitute x t (Term.Boolean false))) (__eo_l_1___mk_quant_var_elim_eq x (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq __eo_lv_x_2) t))))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___mk_quant_var_elim_eq __eo_dv_1 __eo_dv_2)


partial def __eo_prog_quant_var_elim_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)) F)) G) => (__eo_requires (__mk_quant_var_elim_eq x F) G (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)) F)) G))
  | _ => Term.Stuck


partial def __eo_l_1___is_quant_dt_split_conj : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | x, c, Term.__eo_List_nil, F, (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons y) zs)) G) => (__eo_requires (__contains_atomic_term zs y) (Term.Boolean false) (__is_quant_dt_split_conj x (Term.Apply c y) Term.__eo_List_nil F (Term.Apply (Term.Apply Term.forall zs) G)))
  | x, c, Term.__eo_List_nil, F, (Term.Apply (Term.Apply Term.forall Term.__eo_List_nil) G) => (__is_quant_dt_split_conj x c Term.__eo_List_nil F G)
  | x, cx, Term.__eo_List_nil, F, G => (__eo_eq (__substitute x cx F) G)
  | _, _, _, _, _ => Term.Stuck


partial def __is_quant_dt_split_conj : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | x, c, (Term.Apply (Term.Apply Term.__eo_List_cons y) ys), F, (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_y_2) zs)) G) => (__eo_ite (__eo_eq y __eo_lv_y_2) (__eo_requires (__contains_atomic_term zs y) (Term.Boolean false) (__is_quant_dt_split_conj x c ys F (Term.Apply (Term.Apply Term.forall zs) G))) (__eo_l_1___is_quant_dt_split_conj x c (Term.Apply (Term.Apply Term.__eo_List_cons y) ys) F (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_y_2) zs)) G)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3, __eo_dv_4, __eo_dv_5 => (__eo_l_1___is_quant_dt_split_conj __eo_dv_1 __eo_dv_2 __eo_dv_3 __eo_dv_4 __eo_dv_5)


partial def __is_quant_dt_split : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | x, (Term.Apply (Term.Apply Term.__eo_List_cons c) cs), ys, F, (Term.Apply (Term.Apply Term.and g) G) => (__eo_requires (__is_quant_dt_split_conj x c ys F g) (Term.Boolean true) (__is_quant_dt_split x cs ys F G))
  | x, Term.__eo_List_nil, ys, F, (Term.Boolean true) => (Term.Boolean true)
  | x, cs, ys, F, g => (__is_quant_dt_split x cs ys F (Term.Apply (Term.Apply Term.and g) (Term.Boolean true)))


partial def __eo_prog_quant_dt_split : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons x) ys)) F)) G) => (__eo_requires (__is_quant_dt_split x (__dt_get_constructors (__eo_typeof x)) ys F G) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.forall (Term.Apply (Term.Apply Term.__eo_List_cons x) ys)) F)) G))
  | _ => Term.Stuck


partial def __mk_dt_split : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List_nil, x => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.__eo_List_cons c) xs), x => (__eo_cons Term.or (Term.Apply (Term.Apply Term.is c) x) (__mk_dt_split xs x))
  | _, _ => Term.Stuck


partial def __eo_prog_dt_split : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x => (__eo_list_singleton_elim Term.or (__mk_dt_split (__dt_get_constructors (__eo_typeof x)) x))


partial def __mk_dt_inst_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List_nil, x, tb => tb
  | (Term.Apply (Term.Apply Term.__eo_List_cons s) xs), x, t => (__mk_dt_inst_rec xs x (Term.Apply t (Term.Apply s x)))
  | _, _, _ => Term.Stuck


partial def __mk_dt_inst_tuple_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.UnitTuple, x, n => Term.tuple_unit
  | (Term.Apply (Term.Apply Term.Tuple T1) T2), x, n => (__eo_cons Term.tuple (Term.Apply (Term.Apply Term.tuple_select n) x) (__mk_dt_inst_tuple_rec T2 x (__eo_add n (Term.Numeral 1))))
  | _, _, _ => Term.Stuck


partial def __mk_dt_inst : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Tuple T1) T2), Term.tuple, xt => (__mk_dt_inst_tuple_rec (Term.Apply (Term.Apply Term.Tuple T1) T2) xt (Term.Numeral 0))
  | Term.UnitTuple, Term.tuple_unit, xu => Term.tuple_unit
  | D, c, x => (__mk_dt_inst_rec (__dt_get_selectors D c) x (__assoc_nil_nth Term.__eo_List_cons (__eo_dt_constructors D) (__eo_list_find Term.__eo_List_cons (__dt_get_constructors D) c)))


partial def __eo_prog_dt_inst : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) x)) (Term.Apply (Term.Apply Term.eq __eo_lv_x_2) t)) => (__eo_requires (__eo_eq x __eo_lv_x_2) (Term.Boolean true) (__eo_requires (__mk_dt_inst (__eo_typeof x) c x) t (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) x)) (Term.Apply (Term.Apply Term.eq x) t))))
  | _ => Term.Stuck


partial def __eo_prog_dt_collapse_selector : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply s t)) ti) => (__eo_requires (__assoc_nil_nth Term.__eo_List_cons (__dt_arg_list t) (__eo_list_find Term.__eo_List_cons (__dt_get_selectors_of_app (__eo_typeof t) t) s)) ti (Term.Apply (Term.Apply Term.eq (Term.Apply s t)) ti))
  | _ => Term.Stuck


partial def __eo_prog_dt_collapse_tester : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) t)) b) => (__eo_requires (__dt_eq_cons c t) b (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) t)) b))
  | _ => Term.Stuck


partial def __eo_prog_dt_collapse_tester_singleton : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) t)) (Term.Boolean true)) => (__eo_requires (__eo_list_len Term.__eo_List_cons (__dt_get_constructors (__eo_typeof t))) (Term.Numeral 1) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.is c) t)) (Term.Boolean true)))
  | _ => Term.Stuck


partial def __mk_dt_cons_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.tuple a) as), (Term.Apply (Term.Apply Term.tuple b) bs) => (__eo_cons Term.and (Term.Apply (Term.Apply Term.eq a) b) (__mk_dt_cons_eq as bs))
  | (Term.Apply f a), (Term.Apply g b) => (__eo_list_concat Term.and (__mk_dt_cons_eq f g) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq a) b)) (Term.Boolean true)))
  | c, __eo_lv_c_2 => (__eo_requires (__eo_eq c __eo_lv_c_2) (Term.Boolean true) (Term.Boolean true))


partial def __eo_prog_dt_cons_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) => (__eo_requires (__eo_list_singleton_elim Term.and (__mk_dt_cons_eq t s)) B (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B))
  | _ => Term.Stuck


partial def __eo_prog_dt_cons_eq_clash : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) (Term.Boolean false)) => (__eo_requires (__eo_ite (__eo_eq t s) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons t) (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil)) (__eo_typeof t))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __dt_find_cycle_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f a), s, l => (__dt_find_cycle_rec f s (__eo_cons Term.__eo_List_cons a l))
  | c, s, l => (__eo_ite (__eo_ite (__eo_is_eq c Term.tuple) (Term.Boolean true) (__eo_is_ok (__eo_dt_selectors c))) (__dt_find_cycle_list l s) (Term.Boolean false))


partial def __eo_l_1___dt_find_cycle_list : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons t) ts), ss => (__eo_ite (__dt_find_cycle_rec t ss Term.__eo_List_nil) (Term.Boolean true) (__dt_find_cycle_list ts ss))
  | Term.__eo_List_nil, ss => (Term.Boolean false)
  | _, _ => Term.Stuck


partial def __dt_find_cycle_list : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons s) ts), (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_s_2) Term.__eo_List_nil) => (__eo_ite (__eo_eq s __eo_lv_s_2) (Term.Boolean true) (__eo_l_1___dt_find_cycle_list (Term.Apply (Term.Apply Term.__eo_List_cons s) ts) (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_s_2) Term.__eo_List_nil)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___dt_find_cycle_list __eo_dv_1 __eo_dv_2)


partial def __eo_prog_dt_cycle : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t)) (Term.Boolean false)) => (__eo_requires (__dt_find_cycle_rec t (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil) Term.__eo_List_nil) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __dt_collapse_updater_rhs : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply f x), a, (Term.Numeral 0) => (Term.Apply f a)
  | (Term.Apply f x), a, n => (__eo_mk_apply (__dt_collapse_updater_rhs f a (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))) x)
  | _, _, _ => Term.Stuck


partial def __tuple_collapse_updater_rhs : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.tuple b) ts), a, (Term.Numeral 0) => (Term.Apply (Term.Apply Term.tuple a) ts)
  | (Term.Apply (Term.Apply Term.tuple b) ts), a, n => (__eo_cons Term.tuple b (__tuple_collapse_updater_rhs ts a (__eo_add n (Term.Numeral (-1 : eo_lit_Int)))))
  | Term.tuple_unit, a, n => Term.tuple_unit
  | _, _, _ => Term.Stuck


partial def __mk_dt_collapse_updater_rhs : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a) => (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons (__dt_get_selectors_of_app (__eo_typeof t) t) s)) t (__dt_collapse_updater_rhs t a (__eo_add (__eo_add (__eo_len (__dt_get_selectors_of_app (__eo_typeof t) t)) (__eo_list_find Term.__eo_List_cons (__dt_get_selectors_of_app (__eo_typeof t) t) s)) (Term.Numeral (-1 : eo_lit_Int)))))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a) => (__tuple_collapse_updater_rhs t a n)
  | _ => Term.Stuck


partial def __eo_prog_dt_collapse_updater : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t) s) => (__eo_requires (__mk_dt_collapse_updater_rhs t) s (Term.Apply (Term.Apply Term.eq t) s))
  | _ => Term.Stuck


partial def __eo_l_1___dt_updater_elim_rhs : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a), (Term.Apply (Term.Apply Term.__eo_List_cons s1) ss), c => (__dt_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a) ss (Term.Apply c (Term.Apply s1 t)))
  | (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a), Term.__eo_List_nil, cd => cd
  | _, _, _ => Term.Stuck


partial def __dt_updater_elim_rhs : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a), (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_s_2) ss), c => (__eo_ite (__eo_eq s __eo_lv_s_2) (__dt_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a) ss (Term.Apply c a)) (__eo_l_1___dt_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a) (Term.Apply (Term.Apply Term.__eo_List_cons __eo_lv_s_2) ss) c))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___dt_updater_elim_rhs __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __eo_l_1___tuple_updater_elim_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a), (Term.Apply (Term.Apply Term.__eo_List_cons s) ss) => (__eo_cons Term.tuple (Term.Apply s t) (__tuple_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a) ss))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) tu) a), Term.__eo_List_nil => Term.tuple_unit
  | _, _ => Term.Stuck


partial def __tuple_updater_elim_rhs : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a), (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Apply Term.tuple_select __eo_lv_n_2)) ss) => (__eo_ite (__eo_eq n __eo_lv_n_2) (__eo_cons Term.tuple a (__tuple_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a) ss)) (__eo_l_1___tuple_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Apply Term.tuple_select __eo_lv_n_2)) ss)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___tuple_updater_elim_rhs __eo_dv_1 __eo_dv_2)


partial def __mk_dt_updater_elim_rhs : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a), c, ss => (__dt_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.update s) t) a) ss (__assoc_nil_nth Term.__eo_List_cons (__eo_dt_constructors (__eo_typeof t)) (__eo_list_find Term.__eo_List_cons (__dt_get_constructors (__eo_typeof t)) c)))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a), Term.tuple, ss => (__tuple_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply Term.tuple_update n) t) a) ss)
  | _, _, _ => Term.Stuck


partial def __eo_prog_dt_updater_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply u s) t) a)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.is c) __eo_lv_t_2)) tu) __eo_lv_t_3)) => (__eo_requires (__eo_and (__eo_eq t __eo_lv_t_2) (__eo_eq t __eo_lv_t_3)) (Term.Boolean true) (__eo_requires (__mk_dt_updater_elim_rhs (Term.Apply (Term.Apply (Term.Apply u s) t) a) c (__dt_get_selectors (__eo_typeof t) c)) tu (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply u s) t) a)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.is c) t)) tu) t))))
  | _ => Term.Stuck


partial def __eo_prog_arith_div_total_zero_real : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv_total t1) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Rational (eo_lit_mk_rational 0 1)))


partial def __eo_prog_arith_div_total_zero_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv_total t1) (Term.Numeral 0))) (Term.Rational (eo_lit_mk_rational 0 1)))


partial def __eo_prog_arith_int_div_total : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div t1) s1)) (Term.Apply (Term.Apply Term.div_total t1) s1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_int_div_total_one : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 1))) t1)


partial def __eo_prog_arith_int_div_total_zero : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total t1) (Term.Numeral 0))) (Term.Numeral 0))


partial def __eo_prog_arith_int_div_total_neg : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_s1_2) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.div_total t1) s1)) (Term.Apply Term.__eoo_neg_2 (Term.Apply (Term.Apply Term.div_total t1) (Term.Apply Term.__eoo_neg_2 s1)))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_int_mod_total : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod t1) s1)) (Term.Apply (Term.Apply Term.mod_total t1) s1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_int_mod_total_one : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 1))) (Term.Numeral 0))


partial def __eo_prog_arith_int_mod_total_zero : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0))) t1)


partial def __eo_prog_arith_int_mod_total_neg : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_s1_2) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) s1)) (Term.Apply (Term.Apply Term.mod_total t1) (Term.Apply Term.__eoo_neg_2 s1))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_elim_gt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt t1) s1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq s1) t1)))


partial def __eo_prog_arith_elim_lt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt t1) s1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq t1) s1)))


partial def __eo_prog_arith_elim_int_gt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt t1) s1)) (Term.Apply (Term.Apply Term.geq t1) (Term.Apply (Term.Apply Term.plus s1) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))


partial def __eo_prog_arith_elim_int_lt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt t1) s1)) (Term.Apply (Term.Apply Term.geq s1) (Term.Apply (Term.Apply Term.plus t1) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))


partial def __eo_prog_arith_elim_leq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq t1) s1)) (Term.Apply (Term.Apply Term.geq s1) t1))


partial def __eo_prog_arith_leq_norm : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq t1) s1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq t1) (Term.Apply (Term.Apply Term.plus s1) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))))


partial def __eo_prog_arith_geq_tighten : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.geq t1) s1))) (Term.Apply (Term.Apply Term.geq s1) (Term.Apply (Term.Apply Term.plus t1) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0)))))


partial def __eo_prog_arith_geq_norm1_int : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq t1) s1)) (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg t1) s1)) (Term.Numeral 0)))


partial def __eo_prog_arith_geq_norm1_real : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq t1) s1)) (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg t1) s1)) (Term.Rational (eo_lit_mk_rational 0 1))))


partial def __eo_prog_arith_eq_elim_real : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq t1) s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq t1) s1)) (Term.Boolean true))))


partial def __eo_prog_arith_eq_elim_int : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.geq t1) s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq t1) s1)) (Term.Boolean true))))


partial def __eo_prog_arith_to_int_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_int x1)) x1)


partial def __eo_prog_arith_to_int_elim_to_real : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_int (Term.Apply Term.to_real x1))) (Term.Apply Term.to_int x1))


partial def __eo_prog_arith_div_elim_to_real1 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv (Term.Apply Term.to_real x1)) y1)) (Term.Apply (Term.Apply Term.qdiv x1) y1))


partial def __eo_prog_arith_div_elim_to_real2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.qdiv x1) (Term.Apply Term.to_real y1))) (Term.Apply (Term.Apply Term.qdiv x1) y1))


partial def __eo_prog_arith_mod_over_mod_1 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | c1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_c1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq c1 __eo_lv_c1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total (Term.Apply (Term.Apply Term.mod_total r1) c1)) c1)) (Term.Apply (Term.Apply Term.mod_total r1) c1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_mod_over_mod : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | c1, ts1, r1, ss1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_c1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq c1 __eo_lv_c1_2) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.mod_total (__eo_list_concat Term.plus ts1 (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mod_total r1) c1)) ss1))) c1)) (__eo_mk_apply (__eo_mk_apply Term.mod_total (__eo_list_singleton_elim Term.plus (__eo_list_concat Term.plus ts1 (Term.Apply (Term.Apply Term.plus r1) ss1)))) c1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_arith_mod_over_mod_mult : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | c1, ts1, r1, ss1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_c1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq c1 __eo_lv_c1_2) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.mod_total (__eo_list_concat Term.mult ts1 (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.mod_total r1) c1)) ss1))) c1)) (__eo_mk_apply (__eo_mk_apply Term.mod_total (__eo_list_singleton_elim Term.mult (__eo_list_concat Term.mult ts1 (Term.Apply (Term.Apply Term.mult r1) ss1)))) c1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_arith_int_eq_conflict : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, c1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_real (Term.Apply Term.to_int __eo_lv_c1_2))) __eo_lv_c1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq c1 __eo_lv_c1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_real t1)) c1)) (Term.Boolean false)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_int_geq_tighten : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | t1, c1, cc1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.to_real (Term.Apply Term.to_int __eo_lv_c1_2))) __eo_lv_c1_3)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_cc1_2) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.to_int __eo_lv_c1_4)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq cc1 __eo_lv_cc1_2)) (__eo_eq c1 __eo_lv_c1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.to_real t1)) c1)) (Term.Apply (Term.Apply Term.geq t1) cc1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_arith_divisible_elim : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | n1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.divisible n1) t1)) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) n1)) (Term.Numeral 0))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_arith_abs_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.abs x1)) (Term.Apply Term.abs y1))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.__eoo_neg_2 y1))) (Term.Boolean false))))


partial def __eo_prog_arith_abs_int_gt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply Term.abs x1)) (Term.Apply Term.abs y1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq x1) (Term.Numeral 0))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq y1) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.gt x1) y1)) (Term.Apply (Term.Apply Term.gt x1) (Term.Apply Term.__eoo_neg_2 y1)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq y1) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.gt (Term.Apply Term.__eoo_neg_2 x1)) y1)) (Term.Apply (Term.Apply Term.gt (Term.Apply Term.__eoo_neg_2 x1)) (Term.Apply Term.__eoo_neg_2 y1)))))


partial def __eo_prog_arith_abs_real_gt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply Term.abs x1)) (Term.Apply Term.abs y1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq x1) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq y1) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Apply (Term.Apply Term.gt x1) y1)) (Term.Apply (Term.Apply Term.gt x1) (Term.Apply Term.__eoo_neg_2 y1)))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq y1) (Term.Rational (eo_lit_mk_rational 0 1)))) (Term.Apply (Term.Apply Term.gt (Term.Apply Term.__eoo_neg_2 x1)) y1)) (Term.Apply (Term.Apply Term.gt (Term.Apply Term.__eoo_neg_2 x1)) (Term.Apply Term.__eoo_neg_2 y1)))))


partial def __eo_prog_arith_geq_ite_lift : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | C1, t1, s1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1)) (Term.Apply (Term.Apply (Term.Apply Term.ite C1) (Term.Apply (Term.Apply Term.geq t1) r1)) (Term.Apply (Term.Apply Term.geq s1) r1)))


partial def __eo_prog_arith_leq_ite_lift : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | C1, t1, s1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1)) (Term.Apply (Term.Apply (Term.Apply Term.ite C1) (Term.Apply (Term.Apply Term.leq t1) r1)) (Term.Apply (Term.Apply Term.leq s1) r1)))


partial def __eo_prog_arith_min_lt1 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.lt t1) s1)) t1) s1)) t1)) (Term.Boolean true))


partial def __eo_prog_arith_min_lt2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.lt t1) s1)) t1) s1)) s1)) (Term.Boolean true))


partial def __eo_prog_arith_max_geq1 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq t1) s1)) t1) s1)) t1)) (Term.Boolean true))


partial def __eo_prog_arith_max_geq2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq t1) s1)) t1) s1)) s1)) (Term.Boolean true))


partial def __eo_prog_array_read_over_write : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t1, i1, e1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1)) e1)


partial def __eo_prog_array_read_over_write2 : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, i1, j1, e1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_i1_2) __eo_lv_j1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq i1 __eo_lv_i1_2) (__eo_eq j1 __eo_lv_j1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1)) (Term.Apply (Term.Apply Term.select t1) j1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_array_store_overwrite : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t1, i1, e1, f1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.store (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) i1) f1)) (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) f1))


partial def __eo_prog_array_store_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, i1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) (Term.Apply (Term.Apply Term.select t1) i1))) t1)


partial def __eo_prog_array_read_over_write_split : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t1, i1, e1, j1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.select (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) e1)) i1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq i1) j1)) e1) (Term.Apply (Term.Apply Term.select t1) i1)))


partial def __eo_prog_array_store_swap : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, i1, j1, e1, f1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_i1_2) __eo_lv_j1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq i1 __eo_lv_i1_2) (__eo_eq j1 __eo_lv_j1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.store (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1) f1)) (Term.Apply (Term.Apply (Term.Apply Term.store (Term.Apply (Term.Apply (Term.Apply Term.store t1) j1) f1)) i1) e1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bool_double_not_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply Term.not t1))) t1)


partial def __eo_prog_bool_not_true : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | t1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_t1_2) (Term.Boolean false))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1)) (Term.Boolean true)))
  | _, _ => Term.Stuck


partial def __eo_prog_bool_not_false : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | t1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_t1_2) (Term.Boolean true))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1)) (Term.Boolean false)))
  | _, _ => Term.Stuck


partial def __eo_prog_bool_eq_true : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean true))) t1)


partial def __eo_prog_bool_eq_false : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean false))) (Term.Apply Term.not t1))


partial def __eo_prog_bool_eq_nrefl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.not x1))) (Term.Boolean false))


partial def __eo_prog_bool_impl_false1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp t1) (Term.Boolean false))) (Term.Apply Term.not t1))


partial def __eo_prog_bool_impl_false2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp (Term.Boolean false)) t1)) (Term.Boolean true))


partial def __eo_prog_bool_impl_true1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp t1) (Term.Boolean true))) (Term.Boolean true))


partial def __eo_prog_bool_impl_true2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) t1)) t1)


partial def __eo_prog_bool_impl_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp t1) s1)) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t1)) (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false))))


partial def __eo_prog_bool_dual_impl_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp t1) s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp s1) t1)) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.eq t1) s1))


partial def __eo_prog_bool_and_conf : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, w1, ys1, zs1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.and xs1 (__eo_mk_apply (Term.Apply Term.and w1) (__eo_list_concat Term.and ys1 (Term.Apply (Term.Apply Term.and (Term.Apply Term.not w1)) zs1))))) (Term.Boolean false))


partial def __eo_prog_bool_and_conf2 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, w1, ys1, zs1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.and xs1 (__eo_mk_apply (Term.Apply Term.and (Term.Apply Term.not w1)) (__eo_list_concat Term.and ys1 (Term.Apply (Term.Apply Term.and w1) zs1))))) (Term.Boolean false))


partial def __eo_prog_bool_or_taut : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, w1, ys1, zs1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.or xs1 (__eo_mk_apply (Term.Apply Term.or w1) (__eo_list_concat Term.or ys1 (Term.Apply (Term.Apply Term.or (Term.Apply Term.not w1)) zs1))))) (Term.Boolean true))


partial def __eo_prog_bool_or_taut2 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, w1, ys1, zs1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.or xs1 (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not w1)) (__eo_list_concat Term.or ys1 (Term.Apply (Term.Apply Term.or w1) zs1))))) (Term.Boolean true))


partial def __eo_prog_bool_or_de_morgan : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, zs1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.or x1) (Term.Apply (Term.Apply Term.or y1) zs1)))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply Term.not x1)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_list_singleton_elim Term.or (Term.Apply (Term.Apply Term.or y1) zs1)))) (Term.Boolean true))))


partial def __eo_prog_bool_implies_de_morgan : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.imp x1) y1))) (Term.Apply (Term.Apply Term.and x1) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not y1)) (Term.Boolean true))))


partial def __eo_prog_bool_and_de_morgan : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, zs1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.and x1) (Term.Apply (Term.Apply Term.and y1) zs1)))) (__eo_mk_apply (Term.Apply Term.or (Term.Apply Term.not x1)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply Term.not (__eo_list_singleton_elim Term.and (Term.Apply (Term.Apply Term.and y1) zs1)))) (Term.Boolean false))))


partial def __eo_prog_bool_or_and_distrib : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | y1, y2, ys1, z1, zs1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and y1) (Term.Apply (Term.Apply Term.and y2) ys1))) (Term.Apply (Term.Apply Term.or z1) zs1))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or y1) (Term.Apply (Term.Apply Term.or z1) zs1))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.or (__eo_list_singleton_elim Term.and (Term.Apply (Term.Apply Term.and y2) ys1))) (Term.Apply (Term.Apply Term.or z1) zs1))) (Term.Boolean true))))


partial def __eo_prog_bool_implies_or_distrib : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | y1, y2, ys1, z1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.or y1) (Term.Apply (Term.Apply Term.or y2) ys1))) z1)) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.imp y1) z1)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.imp (__eo_list_singleton_elim Term.or (Term.Apply (Term.Apply Term.or y2) ys1))) z1)) (Term.Boolean true))))


partial def __eo_prog_bool_xor_refl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) x1)) (Term.Boolean false))


partial def __eo_prog_bool_xor_nrefl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) (Term.Apply Term.not x1))) (Term.Boolean true))


partial def __eo_prog_bool_xor_false : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) (Term.Boolean false))) x1)


partial def __eo_prog_bool_xor_true : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) (Term.Boolean true))) (Term.Apply Term.not x1))


partial def __eo_prog_bool_xor_comm : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) y1)) (Term.Apply (Term.Apply Term.xor y1) x1))


partial def __eo_prog_bool_xor_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.xor x1) y1)) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not x1)) y1))


partial def __eo_prog_bool_not_xor_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.xor x1) y1))) (Term.Apply (Term.Apply Term.eq x1) y1))


partial def __eo_prog_bool_not_eq_elim1 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x1) y1))) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not x1)) y1))


partial def __eo_prog_bool_not_eq_elim2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x1) y1))) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.not y1)))


partial def __eo_prog_ite_neg_branch : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | c1, x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not __eo_lv_y1_2)) __eo_lv_x1_2)) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)) (Term.Apply (Term.Apply Term.eq c1) x1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_ite_then_true : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean true)) x1)) (Term.Apply (Term.Apply Term.or c1) (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))


partial def __eo_prog_ite_else_false : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Boolean false))) (Term.Apply (Term.Apply Term.and c1) (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))))


partial def __eo_prog_ite_then_false : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean false)) x1)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not c1)) (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))))


partial def __eo_prog_ite_else_true : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Boolean true))) (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1)) (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false))))


partial def __eo_prog_ite_then_lookahead_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) c1) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean true)) x1))


partial def __eo_prog_ite_else_lookahead_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) c1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Boolean false)))


partial def __eo_prog_ite_then_lookahead_not_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply Term.not c1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean false)) x1))


partial def __eo_prog_ite_else_lookahead_not_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Apply Term.not c1))) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Boolean true)))


partial def __eo_prog_ite_expand : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply Term.not c1)) (Term.Apply (Term.Apply Term.or x1) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or c1) (Term.Apply (Term.Apply Term.or y1) (Term.Boolean false)))) (Term.Boolean true))))


partial def __eo_prog_bool_not_ite_elim : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply Term.not x1)) (Term.Apply Term.not y1)))


partial def __eo_prog_ite_true_cond : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean true)) x1) y1)) x1)


partial def __eo_prog_ite_false_cond : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1)) y1)


partial def __eo_prog_ite_not_cond : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) x1) y1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) x1))


partial def __eo_prog_ite_eq_branch : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) x1)) x1)


partial def __eo_prog_ite_then_lookahead : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1)) z1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) z1))


partial def __eo_prog_ite_else_lookahead : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) z1))) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) z1))


partial def __eo_prog_ite_then_neg_lookahead : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) x1) y1)) z1)) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) y1) z1))


partial def __eo_prog_ite_else_neg_lookahead : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply Term.not c1)) y1) z1))) (Term.Apply (Term.Apply (Term.Apply Term.ite c1) x1) y1))


partial def __eo_prog_bv_concat_extract_merge : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, s1, ys1, i1, j1, j2, k1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_j2_2) (Term.Apply (Term.Apply Term.plus __eo_lv_j1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_eq j2 __eo_lv_j2_2) (__eo_eq j1 __eo_lv_j1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract k1) j2) s1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) s1)) ys1)))) (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract k1) i1) s1)) ys1)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_extract : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, i1, j1, k1, l1, ll1, kk1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ll1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_i1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_l1_2) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_kk1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_i1_3) (Term.Apply (Term.Apply Term.plus __eo_lv_k1_2) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ll1 __eo_lv_ll1_2) (__eo_eq i1 __eo_lv_i1_2)) (__eo_eq l1 __eo_lv_l1_2)) (__eo_eq kk1 __eo_lv_kk1_2)) (__eo_eq i1 __eo_lv_i1_3)) (__eo_eq k1 __eo_lv_k1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract l1) k1) (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) x1))) (Term.Apply (Term.Apply (Term.Apply Term.extract ll1) kk1) x1)))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_whole : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract n1) (Term.Numeral 0)) x1)) x1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_concat_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, xs1, y1, i1, j1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq __eo_lv_j1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq j1 __eo_lv_j1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract j1) i1) (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0)))))) (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) x1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_concat_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, xs1, y1, i1, j1, u1, u2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_i1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_j1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_3))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_j1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_4)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_5)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq i1 __eo_lv_i1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq j1 __eo_lv_j1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq j1 __eo_lv_j1_3)) (__eo_eq x1 __eo_lv_x1_4)) (__eo_eq u2 __eo_lv_u2_2)) (__eo_eq x1 __eo_lv_x1_5)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract j1) i1) (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0)))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u2) i1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_concat_3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, y1, xs1, i1, j1, u1, l1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_i1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_j1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_l1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_i1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_4)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq i1 __eo_lv_i1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq j1 __eo_lv_j1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq l1 __eo_lv_l1_2)) (__eo_eq i1 __eo_lv_i1_3)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract j1) i1) (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0)))))) (__eo_mk_apply (Term.Apply (Term.Apply Term.extract u1) l1) (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_concat_4 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, xs1, i1, j1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_j1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_x1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_2) __eo_lv_xs1_2)))) (Term.Apply Term._at_bvsize __eo_lv_x1_3)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq j1 __eo_lv_j1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq xs1 __eo_lv_xs1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract j1) i1) (__eo_mk_apply (Term.Apply Term.concat x1) (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))))) (__eo_mk_apply (Term.Apply (Term.Apply Term.extract j1) i1) (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_eq_extract_elim1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | x1, y1, i1, j1, wm1, jp1, im1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_jp1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_j1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_im1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_i1_2) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_wm1_3) __eo_lv_j1_3)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_i1_3) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq wm1 __eo_lv_wm1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq jp1 __eo_lv_jp1_2)) (__eo_eq j1 __eo_lv_j1_2)) (__eo_eq im1 __eo_lv_im1_2)) (__eo_eq i1 __eo_lv_i1_2)) (__eo_eq wm1 __eo_lv_wm1_3)) (__eo_eq j1 __eo_lv_j1_3)) (__eo_eq i1 __eo_lv_i1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) x1)) y1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) jp1) x1)) (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract im1) (Term.Numeral 0)) x1)) (Term.Binary 0 0)))))))
  | _, _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_eq_extract_elim2 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, y1, j1, wm1, jp1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_jp1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_j1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_wm1_3) __eo_lv_j1_3)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq wm1 __eo_lv_wm1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq jp1 __eo_lv_jp1_2)) (__eo_eq j1 __eo_lv_j1_2)) (__eo_eq wm1 __eo_lv_wm1_3)) (__eo_eq j1 __eo_lv_j1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract j1) (Term.Numeral 0)) x1)) y1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) jp1) x1)) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0))))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_eq_extract_elim3 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, y1, i1, j1, im1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_j1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_im1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_i1_2) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_i1_3) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq j1 __eo_lv_j1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq im1 __eo_lv_im1_2)) (__eo_eq i1 __eo_lv_i1_2)) (__eo_eq i1 __eo_lv_i1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) x1)) y1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract im1) (Term.Numeral 0)) x1)) (Term.Binary 0 0))))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_not : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, i1, j1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) (Term.Apply Term.bvnot x1))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply (Term.Apply Term.extract j1) i1) x1)))


partial def __eo_prog_bv_extract_sign_extend_1 : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, low1, high1, k1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_high1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq high1 __eo_lv_high1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract high1) low1) (Term.Apply (Term.Apply Term.sign_extend k1) x1))) (Term.Apply (Term.Apply (Term.Apply Term.extract high1) low1) x1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_sign_extend_2 : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, low1, high1, k1, nm1, sn1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_low1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_high1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_3))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_sn1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.neg __eo_lv_high1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_5))) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq low1 __eo_lv_low1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq high1 __eo_lv_high1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq x1 __eo_lv_x1_4)) (__eo_eq sn1 __eo_lv_sn1_2)) (__eo_eq high1 __eo_lv_high1_3)) (__eo_eq x1 __eo_lv_x1_5)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract high1) low1) (Term.Apply (Term.Apply Term.sign_extend k1) x1))) (Term.Apply (Term.Apply Term.sign_extend sn1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) low1) x1))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_sign_extend_3 : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, low1, high1, k1, rn1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_low1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_rn1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.neg __eo_lv_high1_2) __eo_lv_low1_3)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq low1 __eo_lv_low1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq rn1 __eo_lv_rn1_2)) (__eo_eq high1 __eo_lv_high1_2)) (__eo_eq low1 __eo_lv_low1_3)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract high1) low1) (Term.Apply (Term.Apply Term.sign_extend k1) x1))) (Term.Apply (Term.Apply Term.repeat rn1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_not_xor : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, x2, xs1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term.bvxor x1) (Term.Apply (Term.Apply Term.bvxor x2) xs1)))) (Term.Apply (Term.Apply Term.bvxor (Term.Apply Term.bvnot x1)) (Term.Apply (Term.Apply Term.bvxor x2) xs1)))


partial def __eo_prog_bv_and_simplify_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, ys1, zs1, x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvand xs1 (__eo_mk_apply (Term.Apply Term.bvand (Term.Apply Term.bvnot x1)) (__eo_list_concat Term.bvand ys1 (Term.Apply (Term.Apply Term.bvand x1) zs1))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_and_simplify_2 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, ys1, zs1, x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvand xs1 (__eo_mk_apply (Term.Apply Term.bvand x1) (__eo_list_concat Term.bvand ys1 (Term.Apply (Term.Apply Term.bvand (Term.Apply Term.bvnot x1)) zs1))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_or_simplify_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, ys1, zs1, x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvor xs1 (__eo_mk_apply (Term.Apply Term.bvor (Term.Apply Term.bvnot x1)) (__eo_list_concat Term.bvor ys1 (Term.Apply (Term.Apply Term.bvor x1) zs1))))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_or_simplify_2 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, ys1, zs1, x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvor xs1 (__eo_mk_apply (Term.Apply Term.bvor x1) (__eo_list_concat Term.bvor ys1 (Term.Apply (Term.Apply Term.bvor (Term.Apply Term.bvnot x1)) zs1))))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_simplify_1 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, ys1, zs1, x1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_list_concat Term.bvxor ys1 (Term.Apply (Term.Apply Term.bvxor x1) zs1))))) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 (__eo_list_concat Term.bvxor ys1 zs1))))


partial def __eo_prog_bv_xor_simplify_2 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, ys1, zs1, x1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_list_concat Term.bvxor ys1 (Term.Apply (Term.Apply Term.bvxor (Term.Apply Term.bvnot x1)) zs1))))) (__eo_mk_apply Term.bvnot (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 (__eo_list_concat Term.bvxor ys1 zs1)))))


partial def __eo_prog_bv_xor_simplify_3 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, ys1, zs1, x1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (__eo_mk_apply (Term.Apply Term.bvxor (Term.Apply Term.bvnot x1)) (__eo_list_concat Term.bvxor ys1 (Term.Apply (Term.Apply Term.bvxor x1) zs1))))) (__eo_mk_apply Term.bvnot (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 (__eo_list_concat Term.bvxor ys1 zs1)))))


partial def __eo_prog_bv_ult_add_one : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, ys1, zs1, c1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_c1_2) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_w1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq w1 __eo_lv_w1_2)) (__eo_eq w1 __eo_lv_w1_3)) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvult x1) (__eo_list_concat Term.bvadd ys1 (Term.Apply (Term.Apply Term.bvadd c1) zs1)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_singleton_elim Term.bvadd (__eo_list_concat Term.bvadd ys1 zs1))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply Term.not (__eo_mk_apply (__eo_mk_apply Term.bvult (__eo_list_singleton_elim Term.bvadd (__eo_list_concat Term.bvadd ys1 zs1))) x1))) (Term.Boolean true)))))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_mult_slt_mult_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, a1, n1, m1, tn1, an1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tn1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_an1_2) (Term.Apply Term._at_bvsize __eo_lv_a1_2))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq tn1 __eo_lv_tn1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq an1 __eo_lv_an1_2)) (__eo_eq a1 __eo_lv_a1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.bvslt (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend n1) y1)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend m1) a1)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend n1) y1)))))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend n1) x1)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend m1) a1)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend n1) x1))))))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsub y1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) tn1)))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) an1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvslt y1) x1)) (Term.Apply (Term.Apply Term.bvsgt a1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) an1)))) (Term.Boolean true))))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_mult_slt_mult_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, a1, n1, m1, tn1, an1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tn1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_an1_2) (Term.Apply Term._at_bvsize __eo_lv_a1_2))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq tn1 __eo_lv_tn1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq an1 __eo_lv_an1_2)) (__eo_eq a1 __eo_lv_a1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.bvslt (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.zero_extend n1) y1)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend m1) a1)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.zero_extend n1) y1)))))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.zero_extend n1) x1)) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.sign_extend m1) a1)) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.zero_extend n1) x1))))))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsub y1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) tn1)))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) an1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult y1) x1)) (Term.Apply (Term.Apply Term.bvsgt a1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) an1)))) (Term.Boolean true))))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_commutative_xor : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof x1))))) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_nil Term.bvxor (__eo_typeof y1)))))


partial def __eo_prog_bv_commutative_comp : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvcomp x1) y1)) (Term.Apply (Term.Apply Term.bvcomp y1) x1))


partial def __eo_prog_bv_zero_extend_eliminate_0 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.zero_extend (Term.Numeral 0)) x1)) x1)


partial def __eo_prog_bv_sign_extend_eliminate_0 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.sign_extend (Term.Numeral 0)) x1)) x1)


partial def __eo_prog_bv_not_neq : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | x1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq x1 __eo_lv_x1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.bvnot x1))) (Term.Boolean false)))
  | _, _ => Term.Stuck


partial def __eo_prog_bv_ult_ones : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_w1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq w1 __eo_lv_w1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult x1) (Term.Apply (Term.Apply Term._at_bv n1) w1))) (Term.Apply Term.distinct (Term.Apply (Term.Apply Term.__eo_List_cons x1) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Apply (Term.Apply Term._at_bv n1) w1)) Term.__eo_List_nil)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_concat_merge_const : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, n1, w1, n2, w2, ww1, zs1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ww1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_w1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_w2_2) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_eq ww1 __eo_lv_ww1_2) (__eo_eq w1 __eo_lv_w1_2)) (__eo_eq w2 __eo_lv_w2_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv n1) w1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv n2) w2)) zs1)))) (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat xs1 (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mult n1) (Term.Apply (Term.Apply Term.mult (Term.Apply Term.int_pow2 w2)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mod n2) (Term.Apply Term.int_pow2 w2))) (Term.Numeral 0)))) ww1)) zs1)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_commutative_add : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvadd x1) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_nil Term.bvadd (__eo_typeof x1))))) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_mk_apply (Term.Apply Term.bvadd x1) (__eo_nil Term.bvadd (__eo_typeof y1)))))


partial def __eo_prog_bv_sub_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsub x1) y1)) (__eo_mk_apply (Term.Apply Term.bvadd x1) (__eo_mk_apply (Term.Apply Term.bvadd (Term.Apply Term.bvneg y1)) (__eo_nil Term.bvadd (__eo_typeof x1)))))


partial def __eo_prog_bv_ite_width_one : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1)


partial def __eo_prog_bv_ite_width_one_not : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply Term.bvnot x1))


partial def __eo_prog_bv_eq_xor_solve : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof x1))))) z1)) (__eo_mk_apply (Term.Apply Term.eq x1) (__eo_mk_apply (Term.Apply Term.bvxor z1) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof z1))))))) (Term.Boolean true))


partial def __eo_prog_bv_eq_not_solve : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvnot x1)) y1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.bvnot y1)))) (Term.Boolean true))


partial def __eo_prog_bv_ugt_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvugt x1) y1)) (Term.Apply (Term.Apply Term.bvult y1) x1))


partial def __eo_prog_bv_uge_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvuge x1) y1)) (Term.Apply (Term.Apply Term.bvule y1) x1))


partial def __eo_prog_bv_sgt_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsgt x1) y1)) (Term.Apply (Term.Apply Term.bvslt y1) x1))


partial def __eo_prog_bv_sge_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsge x1) y1)) (Term.Apply (Term.Apply Term.bvsle y1) x1))


partial def __eo_prog_bv_sle_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsle x1) y1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.bvslt y1) x1)))


partial def __eo_prog_bv_redor_eliminate : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvredor x1)) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term.bvcomp x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_redand_eliminate : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvredand x1)) (Term.Apply (Term.Apply Term.bvcomp x1) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_ule_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule x1) y1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.bvult y1) x1)))


partial def __eo_prog_bv_comp_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvcomp x1) y1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1))))


partial def __eo_prog_bv_rotate_left_eliminate_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, amount1, u1, u2, l1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Numeral 0))) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_4))) (Term.Numeral 0)))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_5)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_l1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_6)) (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_4) (Term.Apply Term._at_bvsize __eo_lv_x1_7))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq amount1 __eo_lv_amount1_3)) (__eo_eq x1 __eo_lv_x1_4)) (__eo_eq u2 __eo_lv_u2_2)) (__eo_eq x1 __eo_lv_x1_5)) (__eo_eq l1 __eo_lv_l1_2)) (__eo_eq x1 __eo_lv_x1_6)) (__eo_eq amount1 __eo_lv_amount1_4)) (__eo_eq x1 __eo_lv_x1_7)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.rotate_left amount1) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u2) l1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_rotate_left_eliminate_2 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, amount1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.rotate_left amount1) x1)) x1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_rotate_right_eliminate_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, amount1, u1, u2, l1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Numeral 0))) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_3) (Term.Apply Term._at_bvsize __eo_lv_x1_3))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_l1_2) (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_4) (Term.Apply Term._at_bvsize __eo_lv_x1_5)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq amount1 __eo_lv_amount1_3)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq u2 __eo_lv_u2_2)) (__eo_eq x1 __eo_lv_x1_4)) (__eo_eq l1 __eo_lv_l1_2)) (__eo_eq amount1 __eo_lv_amount1_4)) (__eo_eq x1 __eo_lv_x1_5)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.rotate_right amount1) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u2) l1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_rotate_right_eliminate_2 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, amount1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.rotate_right amount1) x1)) x1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_nand_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvnand x1) y1)) (__eo_mk_apply Term.bvnot (__eo_mk_apply (Term.Apply Term.bvand x1) (__eo_mk_apply (Term.Apply Term.bvand y1) (__eo_nil Term.bvand (__eo_typeof x1))))))


partial def __eo_prog_bv_nor_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvnor x1) y1)) (__eo_mk_apply Term.bvnot (__eo_mk_apply (Term.Apply Term.bvor x1) (__eo_mk_apply (Term.Apply Term.bvor y1) (__eo_nil Term.bvor (__eo_typeof x1))))))


partial def __eo_prog_bv_xnor_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvxnor x1) y1)) (__eo_mk_apply Term.bvnot (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof x1))))))


partial def __eo_prog_bv_sdiv_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq nm1 __eo_lv_nm1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsdiv x1) y1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.xor (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))))) (Term.Apply Term.bvneg (Term.Apply (Term.Apply Term.bvudiv (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg x1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg y1)) y1)))) (Term.Apply (Term.Apply Term.bvudiv (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg x1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg y1)) y1)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_zero_extend_eliminate : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.zero_extend n1) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0))))


partial def __eo_prog_bv_uaddo_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvuaddo x1) y1)) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract w1) w1) (__eo_mk_apply (Term.Apply Term.bvadd (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0)))) (__eo_mk_apply (Term.Apply Term.bvadd (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))) (__eo_nil Term.bvadd (__eo_typeof (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0))))))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_saddo_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, wm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq wm1 __eo_lv_wm1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsaddo x1) y1)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract wm1) wm1) (__eo_mk_apply (Term.Apply Term.bvadd x1) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_nil Term.bvadd (__eo_typeof x1)))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract wm1) wm1) (__eo_mk_apply (Term.Apply Term.bvadd x1) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_nil Term.bvadd (__eo_typeof x1)))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Boolean false)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sdivo_eliminate : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, w1, wm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_y1_2))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq wm1 __eo_lv_wm1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq w1 __eo_lv_w1_2)) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsdivo x1) y1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) wm1)) (Term.Binary 0 0))))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq y1) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))) (Term.Boolean true)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_smod_eliminate : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, w1, wm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq wm1 __eo_lv_wm1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsmod x1) y1)) (__eo_mk_apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1)))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))) (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1)))) (__eo_mk_apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1)))) (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (__eo_mk_apply (Term.Apply Term.bvadd (Term.Apply Term.bvneg (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1))))) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_nil Term.bvadd (__eo_typeof (Term.Apply Term.bvneg (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1))))))))) (__eo_mk_apply (__eo_mk_apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Boolean true)))) (__eo_mk_apply (Term.Apply Term.bvadd (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1)))) (__eo_mk_apply (Term.Apply Term.bvadd y1) (__eo_nil Term.bvadd (__eo_typeof (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1)))))))) (Term.Apply Term.bvneg (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) x1) (Term.Apply Term.bvneg x1))) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) y1) (Term.Apply Term.bvneg y1))))))))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_srem_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq nm1 __eo_lv_nm1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsrem x1) y1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg x1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg y1)) y1)))) (Term.Apply (Term.Apply Term.bvurem (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg x1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvneg y1)) y1)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_usubo_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvusubo x1) y1)) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract n1) n1) (Term.Apply (Term.Apply Term.bvsub (Term.Apply (Term.Apply Term.zero_extend (Term.Numeral 1)) x1)) (Term.Apply (Term.Apply Term.zero_extend (Term.Numeral 1)) y1)))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_ssubo_eliminate : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq nm1 __eo_lv_nm1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvssubo x1) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) (Term.Apply (Term.Apply Term.bvsub x1) y1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) y1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) (Term.Apply (Term.Apply Term.bvsub x1) y1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Boolean true)))) (Term.Boolean false)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_nego_eliminate : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvnego x1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) (Term.Binary 0 0))))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_ite_equal_children : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | c1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) x1) x1)) x1)


partial def __eo_prog_bv_ite_const_children_1 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | c1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))) (Term.Apply Term.bvnot c1))


partial def __eo_prog_bv_ite_const_children_2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | c1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) c1)


partial def __eo_prog_bv_ite_equal_cond_1 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, t1, e1, e2 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) e1)) e2)) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) e2))


partial def __eo_prog_bv_ite_equal_cond_2 : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, t1, t2, e1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t2) e1))) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) e1))


partial def __eo_prog_bv_ite_equal_cond_3 : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, t1, e1, t2, e2 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) e1)) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t2) e2))) (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) e2))


partial def __eo_prog_bv_ite_merge_then_if : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, c2, t1, e1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c2) t1) e1)) t1)) (Term.Apply (Term.Apply (Term.Apply Term.bvite (Term.Apply (Term.Apply Term.bvand c1) (Term.Apply (Term.Apply Term.bvand (Term.Apply Term.bvnot c2)) (Term.Binary 1 1)))) e1) t1))


partial def __eo_prog_bv_ite_merge_else_if : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, c2, t1, e1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c2) t1) e1)) e1)) (Term.Apply (Term.Apply (Term.Apply Term.bvite (Term.Apply (Term.Apply Term.bvand c1) (Term.Apply (Term.Apply Term.bvand c2) (Term.Binary 1 1)))) t1) e1))


partial def __eo_prog_bv_ite_merge_then_else : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, c2, t1, e1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t1) (Term.Apply (Term.Apply (Term.Apply Term.bvite c2) t1) e1))) (Term.Apply (Term.Apply (Term.Apply Term.bvite (Term.Apply (Term.Apply Term.bvand (Term.Apply Term.bvnot c1)) (Term.Apply (Term.Apply Term.bvand (Term.Apply Term.bvnot c2)) (Term.Binary 1 1)))) e1) t1))


partial def __eo_prog_bv_ite_merge_else_else : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | c1, c2, t1, t2 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.bvite c1) t2) (Term.Apply (Term.Apply (Term.Apply Term.bvite c2) t1) t2))) (Term.Apply (Term.Apply (Term.Apply Term.bvite (Term.Apply (Term.Apply Term.bvand (Term.Apply Term.bvnot c1)) (Term.Apply (Term.Apply Term.bvand c2) (Term.Binary 1 1)))) t1) t2))


partial def __eo_prog_bv_shl_by_const_0 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, sz1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvshl x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) sz1))) x1)


partial def __eo_prog_bv_shl_by_const_1 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, amount1, sz1, en1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_en1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus __eo_lv_amount1_3) (Term.Numeral 0)))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq en1 __eo_lv_en1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq amount1 __eo_lv_amount1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvshl x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract en1) (Term.Numeral 0)) x1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) amount1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_shl_by_const_2 : Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, amount1, sz1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_amount1_3) (Term.Apply Term.int_pow2 (Term.Apply Term._at_bvsize __eo_lv_x1_3)))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_4))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq amount1 __eo_lv_amount1_3)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq w1 __eo_lv_w1_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvshl x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_lshr_by_const_0 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, sz1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvlshr x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) sz1))) x1)


partial def __eo_prog_bv_lshr_by_const_1 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, amount1, sz1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvlshr x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) amount1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) amount1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_lshr_by_const_2 : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, amount1, sz1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_amount1_3) (Term.Apply Term.int_pow2 (Term.Apply Term._at_bvsize __eo_lv_x1_3)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq amount1 __eo_lv_amount1_3)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvlshr x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) sz1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_ashr_by_const_0 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, sz1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvashr x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) sz1))) x1)


partial def __eo_prog_bv_ashr_by_const_1 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, amount1, sz1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvashr x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term.repeat amount1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) amount1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_ashr_by_const_2 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, amount1, sz1, nm1, rn1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_amount1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_rn1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_4))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq amount1 __eo_lv_amount1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq rn1 __eo_lv_rn1_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvashr x1) (Term.Apply (Term.Apply Term._at_bv amount1) sz1))) (Term.Apply (Term.Apply Term.repeat rn1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) nm1) x1))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_and_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply Term._at_bvsize __eo_lv_y1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_2)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq y1 __eo_lv_y1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvand xs1 (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Binary 0 0))))) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvand y1) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_or_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply Term._at_bvsize __eo_lv_y1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_2)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq y1 __eo_lv_y1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvor xs1 (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Binary 0 0))))) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvor y1) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply Term._at_bvsize __eo_lv_y1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_2)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq y1 __eo_lv_y1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_list_singleton_elim Term.concat (__eo_list_concat Term.concat ys1 (Term.Apply (Term.Apply Term.concat z1) (Term.Binary 0 0))))) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_and_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_2) __eo_lv_ys1_2)))) (Term.Apply Term._at_bvsize __eo_lv_z1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_4) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_3)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_5) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_4) __eo_lv_ys1_4)))) (Term.Apply Term._at_bvsize __eo_lv_z1_6))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq z1 __eo_lv_z1_3)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_4)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_3)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq z1 __eo_lv_z1_5)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq ys1 __eo_lv_ys1_4)) (__eo_eq z1 __eo_lv_z1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvand xs1 (Term.Apply (Term.Apply Term.bvand (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) ys1))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvand z1) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_list_singleton_elim Term.concat (Term.Apply (Term.Apply Term.concat y1) ys1))) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_or_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_2) __eo_lv_ys1_2)))) (Term.Apply Term._at_bvsize __eo_lv_z1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_4) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_3)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_5) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_4) __eo_lv_ys1_4)))) (Term.Apply Term._at_bvsize __eo_lv_z1_6))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq z1 __eo_lv_z1_3)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_4)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_3)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq z1 __eo_lv_z1_5)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq ys1 __eo_lv_ys1_4)) (__eo_eq z1 __eo_lv_z1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvor xs1 (Term.Apply (Term.Apply Term.bvor (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) ys1))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvor z1) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_list_singleton_elim Term.concat (Term.Apply (Term.Apply Term.concat y1) ys1))) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, ys1, nxm1, ny1, nym1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_ny1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_2) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_2) __eo_lv_ys1_2)))) (Term.Apply Term._at_bvsize __eo_lv_z1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_4) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_3) __eo_lv_ys1_3)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nym1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize (Term.Apply (Term.Apply Term.concat __eo_lv_z1_5) (Term.Apply (Term.Apply Term.concat __eo_lv_y1_4) __eo_lv_ys1_4)))) (Term.Apply Term._at_bvsize __eo_lv_z1_6))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq ny1 __eo_lv_ny1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq ys1 __eo_lv_ys1_2)) (__eo_eq z1 __eo_lv_z1_3)) (__eo_eq nxm1 __eo_lv_nxm1_2)) (__eo_eq z1 __eo_lv_z1_4)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq ys1 __eo_lv_ys1_3)) (__eo_eq nym1 __eo_lv_nym1_2)) (__eo_eq z1 __eo_lv_z1_5)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq ys1 __eo_lv_ys1_4)) (__eo_eq z1 __eo_lv_z1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (Term.Apply (Term.Apply Term.bvxor (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) ys1))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvxor z1) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) ny1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_list_singleton_elim Term.concat (Term.Apply (Term.Apply Term.concat y1) ys1))) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nym1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_and_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, u1, nxm1, nyu1, nyum1, nu1, num1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_z1_2)) (Term.Numeral 0))))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyu1_2) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_3)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_3)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyum1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_4)) (Term.Numeral 0)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nu1_2) (Term.Apply Term._at_bvsize __eo_lv_u1_5))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_num1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_u1_6)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nxm1 __eo_lv_nxm1_2) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq nyu1 __eo_lv_nyu1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq u1 __eo_lv_u1_3)) (__eo_eq nyum1 __eo_lv_nyum1_2)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq u1 __eo_lv_u1_4)) (__eo_eq nu1 __eo_lv_nu1_2)) (__eo_eq u1 __eo_lv_u1_5)) (__eo_eq num1 __eo_lv_num1_2)) (__eo_eq u1 __eo_lv_u1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvand xs1 (Term.Apply (Term.Apply Term.bvand (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat u1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvand z1) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvand y1) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvand (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvand u1) (__eo_nil Term.bvand (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvand (__eo_list_concat Term.bvand xs1 ws1)))))))) (Term.Binary 0 0))))))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_or_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, u1, nxm1, nyu1, nyum1, nu1, num1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_z1_2)) (Term.Numeral 0))))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyu1_2) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_3)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_3)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyum1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_4)) (Term.Numeral 0)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nu1_2) (Term.Apply Term._at_bvsize __eo_lv_u1_5))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_num1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_u1_6)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nxm1 __eo_lv_nxm1_2) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq nyu1 __eo_lv_nyu1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq u1 __eo_lv_u1_3)) (__eo_eq nyum1 __eo_lv_nyum1_2)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq u1 __eo_lv_u1_4)) (__eo_eq nu1 __eo_lv_nu1_2)) (__eo_eq u1 __eo_lv_u1_5)) (__eo_eq num1 __eo_lv_num1_2)) (__eo_eq u1 __eo_lv_u1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvor xs1 (Term.Apply (Term.Apply Term.bvor (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat u1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvor z1) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvor y1) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvor u1) (__eo_nil Term.bvor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvor (__eo_list_concat Term.bvor xs1 ws1)))))))) (Term.Binary 0 0))))))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | xs1, ws1, y1, z1, u1, nxm1, nyu1, nyum1, nu1, num1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nxm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_2)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_z1_2)) (Term.Numeral 0))))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyu1_2) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_3)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_3)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nyum1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_y1_4)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_u1_4)) (Term.Numeral 0)))) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nu1_2) (Term.Apply Term._at_bvsize __eo_lv_u1_5))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_num1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_u1_6)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nxm1 __eo_lv_nxm1_2) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq nyu1 __eo_lv_nyu1_2)) (__eo_eq y1 __eo_lv_y1_3)) (__eo_eq u1 __eo_lv_u1_3)) (__eo_eq nyum1 __eo_lv_nyum1_2)) (__eo_eq y1 __eo_lv_y1_4)) (__eo_eq u1 __eo_lv_u1_4)) (__eo_eq nu1 __eo_lv_nu1_2)) (__eo_eq u1 __eo_lv_u1_5)) (__eo_eq num1 __eo_lv_num1_2)) (__eo_eq u1 __eo_lv_u1_6)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (Term.Apply (Term.Apply Term.bvxor (Term.Apply (Term.Apply Term.concat z1) (Term.Apply (Term.Apply Term.concat y1) (Term.Apply (Term.Apply Term.concat u1) (Term.Binary 0 0))))) ws1))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvxor z1) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nxm1) nyu1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract nyum1) nu1) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (__eo_mk_apply Term.bvxor (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))) (__eo_mk_apply (Term.Apply Term.bvxor u1) (__eo_nil Term.bvxor (__eo_typeof (__eo_mk_apply (Term.Apply (Term.Apply Term.extract num1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 ws1)))))))) (Term.Binary 0 0))))))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_duplicate : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_nil Term.bvxor (__eo_typeof x1))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_ones : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, zs1, n1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_w1_2)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq w1 __eo_lv_w1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvxor xs1 (Term.Apply (Term.Apply Term.bvxor (Term.Apply (Term.Apply Term._at_bv n1) w1)) zs1))) (__eo_mk_apply Term.bvnot (__eo_list_singleton_elim Term.bvxor (__eo_list_concat Term.bvxor xs1 zs1)))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_xor_not : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvxor (Term.Apply Term.bvnot x1)) (__eo_mk_apply (Term.Apply Term.bvxor (Term.Apply Term.bvnot y1)) (__eo_nil Term.bvxor (__eo_typeof (Term.Apply Term.bvnot x1)))))) (__eo_mk_apply (Term.Apply Term.bvxor x1) (__eo_mk_apply (Term.Apply Term.bvxor y1) (__eo_nil Term.bvxor (__eo_typeof x1)))))


partial def __eo_prog_bv_not_idemp : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.bvnot (Term.Apply Term.bvnot x1))) x1)


partial def __eo_prog_bv_ult_zero_1 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) x1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))))


partial def __eo_prog_bv_ult_zero_2 : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))) (Term.Boolean false))


partial def __eo_prog_bv_ult_self : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult x1) x1)) (Term.Boolean false))


partial def __eo_prog_bv_lt_self : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvslt x1) x1)) (Term.Boolean false))


partial def __eo_prog_bv_ule_self : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule x1) x1)) (Term.Boolean true))


partial def __eo_prog_bv_ule_zero : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)))


partial def __eo_prog_bv_zero_ule : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) x1)) (Term.Boolean true))


partial def __eo_prog_bv_sle_self : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvsle x1) x1)) (Term.Boolean true))


partial def __eo_prog_bv_ule_max : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, n1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 (Term.Apply Term._at_bvsize __eo_lv_x1_3))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq x1 __eo_lv_x1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule x1) (Term.Apply (Term.Apply Term._at_bv n1) w1))) (Term.Boolean true)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_not_ult : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not (Term.Apply (Term.Apply Term.bvult x1) y1))) (Term.Apply (Term.Apply Term.bvule y1) x1))


partial def __eo_prog_bv_mult_pow2_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ys1, z1, size1, n1, exponent1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_ispow2 __eo_lv_n1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_exponent1_2) (Term.Apply Term.int_log2 __eo_lv_n1_3))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg __eo_lv_size1_2) (Term.Apply Term.int_log2 __eo_lv_n1_4))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq exponent1 __eo_lv_exponent1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq size1 __eo_lv_size1_2)) (__eo_eq n1 __eo_lv_n1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvmul xs1 (Term.Apply (Term.Apply Term.bvmul z1) (Term.Apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term._at_bv n1) size1)) ys1)))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) (__eo_list_singleton_elim Term.bvmul (__eo_list_concat Term.bvmul xs1 (Term.Apply (Term.Apply Term.bvmul z1) ys1))))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) exponent1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_mult_pow2_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | xs1, ys1, z1, size1, n1, exponent1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_ispow2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_2)) __eo_lv_n1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_exponent1_2) (Term.Apply Term.int_log2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_3)) __eo_lv_n1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg __eo_lv_size1_4) (Term.Apply Term.int_log2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_5)) __eo_lv_n1_4)))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq size1 __eo_lv_size1_2) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq exponent1 __eo_lv_exponent1_2)) (__eo_eq size1 __eo_lv_size1_3)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq size1 __eo_lv_size1_4)) (__eo_eq size1 __eo_lv_size1_5)) (__eo_eq n1 __eo_lv_n1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.bvmul xs1 (Term.Apply (Term.Apply Term.bvmul z1) (Term.Apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term._at_bv n1) size1)) ys1)))) (__eo_mk_apply (__eo_mk_apply Term.concat (__eo_mk_apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) (__eo_mk_apply Term.bvneg (__eo_list_singleton_elim Term.bvmul (__eo_list_concat Term.bvmul xs1 (Term.Apply (Term.Apply Term.bvmul z1) ys1)))))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) exponent1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_mult_pow2_2b : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | z1, size1, n1, exponent1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_ispow2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_2)) __eo_lv_n1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_exponent1_2) (Term.Apply Term.int_log2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_3)) __eo_lv_n1_3)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_u1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg __eo_lv_size1_4) (Term.Apply Term.int_log2 (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_pow2 __eo_lv_size1_5)) __eo_lv_n1_4)))) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq size1 __eo_lv_size1_2) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq exponent1 __eo_lv_exponent1_2)) (__eo_eq size1 __eo_lv_size1_3)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq size1 __eo_lv_size1_4)) (__eo_eq size1 __eo_lv_size1_5)) (__eo_eq n1 __eo_lv_n1_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.bvmul z1) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term._at_bv n1) size1)) (__eo_nil Term.bvmul (__eo_typeof z1))))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract u1) (Term.Numeral 0)) (Term.Apply Term.bvneg z1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) exponent1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_extract_mult_leading_bit : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | high1, low1, x1i1, x1in1, x1, y1i1, y1in1, y1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply (Term.Apply Term.plus __eo_lv_x1in1_2) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 0)))) (Term.Numeral 64))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.mult (Term.Numeral 2)) (Term.Apply (Term.Apply Term.mult (Term.Apply (Term.Apply Term.plus __eo_lv_x1in1_3) (Term.Apply (Term.Apply Term.plus (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 0)))) (Term.Numeral 1)))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq __eo_lv_x1i1_2) (Term.Numeral 0))) __eo_lv_x1in1_4) (Term.Apply (Term.Apply Term.neg __eo_lv_x1in1_5) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.int_log2 __eo_lv_x1i1_3)) (Term.Numeral 0)))))) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq __eo_lv_y1i1_2) (Term.Numeral 0))) __eo_lv_y1in1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_y1in1_3) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.int_log2 __eo_lv_y1i1_3)) (Term.Numeral 0)))))) (Term.Numeral 0))))) __eo_lv_low1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply Term.neg __eo_lv_high1_2) __eo_lv_low1_3)) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq x1in1 __eo_lv_x1in1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq x1in1 __eo_lv_x1in1_3)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq x1i1 __eo_lv_x1i1_2)) (__eo_eq x1in1 __eo_lv_x1in1_4)) (__eo_eq x1in1 __eo_lv_x1in1_5)) (__eo_eq x1i1 __eo_lv_x1i1_3)) (__eo_eq y1i1 __eo_lv_y1i1_2)) (__eo_eq y1in1 __eo_lv_y1in1_2)) (__eo_eq y1in1 __eo_lv_y1in1_3)) (__eo_eq y1i1 __eo_lv_y1i1_3)) (__eo_eq low1 __eo_lv_low1_2)) (__eo_eq w1 __eo_lv_w1_2)) (__eo_eq high1 __eo_lv_high1_2)) (__eo_eq low1 __eo_lv_low1_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply (Term.Apply Term.extract high1) low1) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv x1i1) x1in1)) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0)))) (__eo_mk_apply (Term.Apply Term.bvmul (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv y1i1) y1in1)) (Term.Apply (Term.Apply Term.concat y1) (Term.Binary 0 0)))) (__eo_nil Term.bvmul (__eo_typeof (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv x1i1) x1in1)) (Term.Apply (Term.Apply Term.concat x1) (Term.Binary 0 0))))))))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_udiv_pow2_not_one : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, v1, n1, power1, nm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_ispow2 __eo_lv_v1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_v1_3) (Term.Numeral 1))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_power1_2) (Term.Apply Term.int_log2 __eo_lv_v1_4))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_n1_2) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq v1 __eo_lv_v1_2) (__eo_eq v1 __eo_lv_v1_3)) (__eo_eq power1 __eo_lv_power1_2)) (__eo_eq v1 __eo_lv_v1_4)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq n1 __eo_lv_n1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvudiv x1) (Term.Apply (Term.Apply Term._at_bv v1) n1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) power1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract nm1) power1) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_udiv_zero : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvudiv x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)))


partial def __eo_prog_bv_udiv_one : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvudiv x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) n1))) x1)


partial def __eo_prog_bv_urem_pow2_not_one : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | x1, v1, n1, nmp1, pm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.int_ispow2 __eo_lv_v1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_v1_3) (Term.Numeral 1))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nmp1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_n1_2) (Term.Apply Term.int_log2 __eo_lv_v1_4)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_pm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.int_log2 __eo_lv_v1_5)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq v1 __eo_lv_v1_2) (__eo_eq v1 __eo_lv_v1_3)) (__eo_eq nmp1 __eo_lv_nmp1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq v1 __eo_lv_v1_4)) (__eo_eq pm1 __eo_lv_pm1_2)) (__eo_eq v1 __eo_lv_v1_5)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvurem x1) (Term.Apply (Term.Apply Term._at_bv v1) n1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) nmp1)) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply (Term.Apply Term.extract pm1) (Term.Numeral 0)) x1)) (Term.Binary 0 0)))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_urem_one : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvurem x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) n1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))


partial def __eo_prog_bv_urem_self : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvurem x1) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_shl_zero : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | a1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) a1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))


partial def __eo_prog_bv_lshr_zero : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | a1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvlshr (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) a1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))


partial def __eo_prog_bv_ashr_zero : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | a1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvashr (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) a1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))


partial def __eo_prog_bv_ugt_urem : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | y1, x1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_y1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvugt (Term.Apply (Term.Apply Term.bvurem y1) x1)) x1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.bvugt y1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) w1))) (Term.Boolean true)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_ult_one : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq x1 __eo_lv_x1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) n1))) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1))))
  | _, _, _ => Term.Stuck


partial def __eo_prog_bv_merge_sign_extend_1 : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, i1, j1, k1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_k1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_i1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_j1_2) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_eq k1 __eo_lv_k1_2) (__eo_eq i1 __eo_lv_i1_2)) (__eo_eq j1 __eo_lv_j1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.sign_extend i1) (Term.Apply (Term.Apply Term.sign_extend j1) x1))) (Term.Apply (Term.Apply Term.sign_extend k1) x1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_merge_sign_extend_2 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, i1, j1, k1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_j1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_k1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_i1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_j1_3) (Term.Numeral 0))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq j1 __eo_lv_j1_2) (__eo_eq k1 __eo_lv_k1_2)) (__eo_eq i1 __eo_lv_i1_2)) (__eo_eq j1 __eo_lv_j1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.sign_extend i1) (Term.Apply (Term.Apply Term.zero_extend j1) x1))) (Term.Apply (Term.Apply Term.zero_extend k1) x1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_eq_const_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, mp1, nm2, nmm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_mp1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_m1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nmm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_nm1_2) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq mp1 __eo_lv_mp1_2) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nmm1 __eo_lv_nmm1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.sign_extend m1) x1)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) mp1))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) mp1)))) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))) (Term.Boolean true)))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_eq_const_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, mp1, nm2, nmm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_mp1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_m1_2) (Term.Apply (Term.Apply Term.plus (Term.Numeral 1)) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nmm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_nm1_2) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq mp1 __eo_lv_mp1_2) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nmm1 __eo_lv_nmm1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_bv c1) nm1)) (Term.Apply (Term.Apply Term.sign_extend m1) x1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) mp1))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) mp1)))) (Term.Boolean false)))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))) (Term.Boolean true)))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_zero_extend_eq_const_1 : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, nmm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nmm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_nm1_2) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq nm2 __eo_lv_nm2_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nmm1 __eo_lv_nmm1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.zero_extend m1) x1)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) m1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))) (Term.Boolean true)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_zero_extend_eq_const_2 : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, nmm1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nmm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_nm1_2) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq nm2 __eo_lv_nm2_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nmm1 __eo_lv_nmm1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_bv c1) nm1)) (Term.Apply (Term.Apply Term.zero_extend m1) x1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nmm1) nm2) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) m1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))) (Term.Boolean true)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_zero_extend_ult_const_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_2)) (Term.Apply (Term.Apply Term.zero_extend __eo_lv_m1_2) (Term.Apply (Term.Apply (Term.Apply Term.extract __eo_lv_nm2_3) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_3))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nm2 __eo_lv_nm2_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq c1 __eo_lv_c1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq nm2 __eo_lv_nm2_3)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term.zero_extend m1) x1)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term.bvult x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_zero_extend_ult_const_2 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_2)) (Term.Apply (Term.Apply Term.zero_extend __eo_lv_m1_2) (Term.Apply (Term.Apply (Term.Apply Term.extract __eo_lv_nm2_3) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_3))))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nm2 __eo_lv_nm2_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq c1 __eo_lv_c1_2)) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq nm2 __eo_lv_nm2_3)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term._at_bv c1) nm1)) (Term.Apply (Term.Apply Term.zero_extend m1) x1))) (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) x1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_ult_const_1 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.bvule (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_2)) (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_nm1_3)) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1))) __eo_lv_nm1_4)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.bvuge (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_5)) (Term.Apply (Term.Apply Term.bvshl (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) __eo_lv_nm1_6))) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1))) __eo_lv_nm1_7)))) (Term.Boolean false)))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq nm1 __eo_lv_nm1_3)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_4)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_5)) (__eo_eq nm1 __eo_lv_nm1_6)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq nm1 __eo_lv_nm1_7)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term.sign_extend m1) x1)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term.bvult x1) (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1)))))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_ult_const_2 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_nm1_2)) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1))) __eo_lv_nm1_3))) (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_4))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_5)) (Term.Apply (Term.Apply Term.bvshl (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) __eo_lv_nm1_6))) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1))) __eo_lv_nm1_7)))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nm1 __eo_lv_nm1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_3)) (__eo_eq c1 __eo_lv_c1_2)) (__eo_eq nm1 __eo_lv_nm1_4)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_5)) (__eo_eq nm1 __eo_lv_nm1_6)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq nm1 __eo_lv_nm1_7)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term.sign_extend m1) x1)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) nm2) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_ult_const_3 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_2)) (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_nm1_3)) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1))) __eo_lv_nm1_4)))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.bvuge (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_5)) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_nm1_6)) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1))) __eo_lv_nm1_7))))) (Term.Boolean false)))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq nm1 __eo_lv_nm1_2)) (__eo_eq nm1 __eo_lv_nm1_3)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_4)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_5)) (__eo_eq nm1 __eo_lv_nm1_6)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq nm1 __eo_lv_nm1_7)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term._at_bv c1) nm1)) (Term.Apply (Term.Apply Term.sign_extend m1) x1))) (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) (Term.Numeral 0)) (Term.Apply (Term.Apply Term._at_bv c1) nm1))) x1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_bv_sign_extend_ult_const_4 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | x1, m1, c1, nm1, nm2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term.bvshl (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) __eo_lv_nm1_2))) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_2)) (Term.Numeral 1))) __eo_lv_nm1_3)))) (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_2) __eo_lv_nm1_4))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule (Term.Apply (Term.Apply Term._at_bv __eo_lv_c1_3) __eo_lv_nm1_5)) (Term.Apply Term.bvnot (Term.Apply (Term.Apply Term.bvshl (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) __eo_lv_nm1_6)) (Term.Apply (Term.Apply Term._at_bv (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_3)) (Term.Numeral 1))) __eo_lv_nm1_7))))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_nm2_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_x1_4)) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq nm1 __eo_lv_nm1_2) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq nm1 __eo_lv_nm1_3)) (__eo_eq c1 __eo_lv_c1_2)) (__eo_eq nm1 __eo_lv_nm1_4)) (__eo_eq c1 __eo_lv_c1_3)) (__eo_eq nm1 __eo_lv_nm1_5)) (__eo_eq nm1 __eo_lv_nm1_6)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq nm1 __eo_lv_nm1_7)) (__eo_eq nm2 __eo_lv_nm2_2)) (__eo_eq x1 __eo_lv_x1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult (Term.Apply (Term.Apply Term._at_bv c1) nm1)) (Term.Apply (Term.Apply Term.sign_extend m1) x1))) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract nm2) nm2) x1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 1)) (Term.Numeral 1)))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_eq_singleton_emp : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_x1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T0_2)))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq _at_T0 __eo_lv__at_T0_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.set_singleton y1))) (Term.Boolean false)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_member_singleton : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member x1) (Term.Apply Term.set_singleton y1))) (Term.Apply (Term.Apply Term.eq x1) y1))


partial def __eo_prog_sets_member_emp : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T1), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_y1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T1_2)))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq _at_T1 __eo_lv__at_T1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member x1) y1)) (Term.Boolean false)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_subset_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_subset x1) y1)) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x1) y1)) y1))


partial def __eo_prog_sets_union_comm : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x1) y1)) (Term.Apply (Term.Apply Term.set_union y1) x1))


partial def __eo_prog_sets_inter_comm : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_inter x1) y1)) (Term.Apply (Term.Apply Term.set_inter y1) x1))


partial def __eo_prog_sets_inter_emp1 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_x1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T0_2)))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq _at_T0 __eo_lv__at_T0_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_inter x1) y1)) x1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_inter_emp2 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T1), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_y1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T1_2)))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq _at_T1 __eo_lv__at_T1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_inter x1) y1)) y1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_minus_emp1 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_x1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T0_2)))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq _at_T0 __eo_lv__at_T0_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_minus x1) y1)) x1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_minus_emp2 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T1), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_y1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T1_2)))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq _at_T1 __eo_lv__at_T1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_minus x1) y1)) x1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_union_emp1 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_x1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T0_2)))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq _at_T0 __eo_lv__at_T0_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x1) y1)) y1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_union_emp2 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Set _at_T1), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_y1_2) (Term.set_empty (Term.Apply Term.Set __eo_lv__at_T1_2)))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq _at_T1 __eo_lv__at_T1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_union x1) y1)) x1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_sets_inter_member : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member x1) (Term.Apply (Term.Apply Term.set_inter y1) z1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.set_member x1) y1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.set_member x1) z1)) (Term.Boolean true))))


partial def __eo_prog_sets_minus_member : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member x1) (Term.Apply (Term.Apply Term.set_minus y1) z1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.set_member x1) y1)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.set_member x1) z1))) (Term.Boolean true))))


partial def __eo_prog_sets_union_member : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_member x1) (Term.Apply (Term.Apply Term.set_union y1) z1))) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.set_member x1) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.set_member x1) z1)) (Term.Boolean false))))


partial def __eo_prog_sets_choose_singleton : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.set_choose (Term.Apply Term.set_singleton x1))) x1)


partial def __eo_prog_sets_minus_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, (Term.Apply Term.Set _at_T0) => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.set_minus x1) x1)) (Term.set_empty (Term.Apply Term.Set _at_T0)))
  | _, _ => Term.Stuck


partial def __eo_prog_sets_is_empty_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, (Term.Apply Term.Set _at_T0) => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.set_is_empty x1)) (Term.Apply (Term.Apply Term.eq x1) (Term.set_empty (Term.Apply Term.Set _at_T0))))
  | _, _ => Term.Stuck


partial def __eo_prog_sets_is_singleton_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.set_is_singleton x1)) (Term.Apply (Term.Apply Term.eq x1) (Term.Apply Term.set_singleton (Term.Apply Term.set_choose x1))))


partial def __eo_prog_str_eq_ctn_false : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, x2, x3, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_x2_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq x2 __eo_lv_x2_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.str_concat x1 (Term.Apply (Term.Apply Term.str_concat x2) x3))) y1)) (Term.Boolean false)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_ctn_full_false1 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_x1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Boolean false)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_ctn_full_false2 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_x1_2) __eo_lv_y1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Boolean false)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_len_false : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_x1_2)) (Term.Apply Term.str_len __eo_lv_y1_2))) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Boolean false)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_empty_str : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_x1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq x1 __eo_lv_x1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) m1)) x1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_empty_range : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, m1, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Numeral 0)) __eo_lv_m1_2)) (Term.Boolean true))) => (__eo_requires (__eo_eq m1 __eo_lv_m1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) m1)) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_empty_start : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, m1, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) m1)) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_empty_start_neg : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, m1, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) m1)) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_substr_start_geq_len : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, m1, n2, m2, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n2_2) __eo_lv_m1_2)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n2 __eo_lv_n2_2) (__eo_eq m1 __eo_lv_m1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) m1)) n2) m2)) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_eq_empty : Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, r1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_m1_2) __eo_lv_n1_3)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_r1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) r1)) (Term.Apply (Term.Apply Term.eq s1) r1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_z_eq_empty_leq : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, r1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 0))) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_r1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Numeral 0)) m1)) r1)) (Term.Apply (Term.Apply Term.leq m1) (Term.Numeral 0))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_eq_empty_leq_len : Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, emp1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_m1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq emp1 __eo_lv_emp1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) emp1)) (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_len s1)) n1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_len_replace_inv : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply Term.str_len __eo_lv_r1_2))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) s1) r1))) (Term.Apply Term.str_len t1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_len_replace_all_inv : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply Term.str_len __eo_lv_r1_2))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t1) s1) r1))) (Term.Apply Term.str_len t1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_len_update_inv : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t1, n1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_update t1) n1) r1))) (Term.Apply Term.str_len t1))


partial def __eo_prog_str_update_in_first_concat : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | t1, ts1, s1, n1, tpre1, tpost1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt (Term.Apply (Term.Apply Term.plus __eo_lv_n1_3) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 0)))) (Term.Apply Term.str_len __eo_lv_t1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpre1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_3) (Term.Numeral 0)) __eo_lv_n1_4))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpost1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_4) (Term.Apply (Term.Apply Term.plus __eo_lv_n1_5) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len __eo_lv_s1_3)) (Term.Numeral 0)))) (Term.Apply Term.str_len __eo_lv_t1_5)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq tpre1 __eo_lv_tpre1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq n1 __eo_lv_n1_4)) (__eo_eq tpost1 __eo_lv_tpost1_2)) (__eo_eq t1 __eo_lv_t1_4)) (__eo_eq n1 __eo_lv_n1_5)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq t1 __eo_lv_t1_5)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_update (Term.Apply (Term.Apply Term.str_concat t1) ts1)) n1) s1)) (Term.Apply (Term.Apply Term.str_concat tpre1) (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat tpost1) ts1)))))
  | _, _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_len_substr_in_range : Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_m1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply (Term.Apply Term.plus __eo_lv_n1_3) (Term.Apply (Term.Apply Term.plus __eo_lv_m1_3) (Term.Numeral 0))))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq m1 __eo_lv_m1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1))) m1))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_clash : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, s2, t1, t2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) __eo_lv_t1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_3)) (Term.Apply Term.str_len __eo_lv_t1_3))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_concat s1) s2)) (Term.Apply (Term.Apply Term.str_concat t1) t2))) (Term.Boolean false)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_clash_rev : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, s2, t1, t2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) __eo_lv_t1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_3)) (Term.Apply Term.str_len __eo_lv_t1_3))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.str_concat s2 (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_nil Term.str_concat (__eo_typeof s2))))) (__eo_list_concat Term.str_concat t2 (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof t2)))))) (Term.Boolean false)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_clash2 : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, t2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) __eo_lv_t1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_3)) (Term.Apply Term.str_len __eo_lv_t1_3))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s1) (Term.Apply (Term.Apply Term.str_concat t1) t2))) (Term.Boolean false)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_clash2_rev : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, t2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) __eo_lv_t1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_3)) (Term.Apply Term.str_len __eo_lv_t1_3))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.eq s1) (__eo_list_concat Term.str_concat t2 (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof t2)))))) (Term.Boolean false)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_unify : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3, t1, t2 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3))) (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat t1) t2)))) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3))) (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat t1) t2))))


partial def __eo_prog_str_concat_unify_rev : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3, t1, t2 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.str_concat s2) (__eo_list_concat Term.str_concat s3 (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_nil Term.str_concat (__eo_typeof s2)))))) (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_list_concat Term.str_concat t2 (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_nil Term.str_concat (__eo_typeof t1))))))) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3))) (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat t1) t2))))


partial def __eo_prog_str_concat_unify_base : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, t1, t2, (Term.Apply Term.Seq _at_T0) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s1) (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat t1) t2)))) (__eo_mk_apply (__eo_mk_apply Term.eq (__seq_empty (Term.Apply Term.Seq _at_T0))) (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat t1) t2))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_concat_unify_base_rev : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, t1, t2, (Term.Apply Term.Seq _at_T0) => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.eq s1) (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_list_concat Term.str_concat t2 (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_nil Term.str_concat (__eo_typeof t1))))))) (__eo_mk_apply (__eo_mk_apply Term.eq (__seq_empty (Term.Apply Term.Seq _at_T0))) (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat t1) t2))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_prefixof_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s1, t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_prefixof s1) t1)) (Term.Apply (Term.Apply Term.eq s1) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t1) (Term.Numeral 0)) (Term.Apply Term.str_len s1))))


partial def __eo_prog_str_suffixof_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s1, t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_suffixof s1) t1)) (Term.Apply (Term.Apply Term.eq s1) (Term.Apply (Term.Apply (Term.Apply Term.str_substr t1) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.str_len t1)) (Term.Apply Term.str_len s1))) (Term.Apply Term.str_len s1))))


partial def __eo_prog_str_prefixof_eq : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply Term.str_len __eo_lv_t1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_prefixof s1) t1)) (Term.Apply (Term.Apply Term.eq s1) t1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_suffixof_eq : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply Term.str_len __eo_lv_t1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_suffixof s1) t1)) (Term.Apply (Term.Apply Term.eq s1) t1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_prefixof_one : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_prefixof s1) t1)) (Term.Apply (Term.Apply Term.str_contains t1) s1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_suffixof_one : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_suffixof s1) t1)) (Term.Apply (Term.Apply Term.str_contains t1) s1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_combine1 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, n1, m1, n2, m2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n2_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg __eo_lv_m2_2) (Term.Apply (Term.Apply Term.neg __eo_lv_m1_2) __eo_lv_n2_3))) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq n2 __eo_lv_n2_2)) (__eo_eq m2 __eo_lv_m2_2)) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq n2 __eo_lv_n2_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) n2) m2)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg m1) n2))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_combine2 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, n1, m1, n2, m2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n2_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.neg (Term.Apply (Term.Apply Term.neg __eo_lv_m1_2) __eo_lv_n2_3)) __eo_lv_m2_2)) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq n2 __eo_lv_n2_2)) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq n2 __eo_lv_n2_3)) (__eo_eq m2 __eo_lv_m2_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) n2) m2)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))) m2)))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_combine3 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, n1, m1, n2, m2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n2_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_s1_2) __eo_lv_n1_3) __eo_lv_m1_2))) (Term.Apply (Term.Apply Term.plus __eo_lv_n2_3) (Term.Apply (Term.Apply Term.plus __eo_lv_m2_2) (Term.Numeral 0))))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq n2 __eo_lv_n2_2)) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq m1 __eo_lv_m1_2)) (__eo_eq n2 __eo_lv_n2_3)) (__eo_eq m2 __eo_lv_m2_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) n2) m2)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))) m2)))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_combine4 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, n1, m1, n2, m2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n2_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply Term.plus __eo_lv_n2_3) (Term.Apply (Term.Apply Term.plus __eo_lv_m2_2) (Term.Numeral 0)))) (Term.Apply Term.str_len (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_s1_2) __eo_lv_n1_3) __eo_lv_m1_2)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq n2 __eo_lv_n2_2)) (__eo_eq n2 __eo_lv_n2_3)) (__eo_eq m2 __eo_lv_m2_2)) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq m1 __eo_lv_m1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) n2) m2)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Apply (Term.Apply Term.plus n1) (Term.Apply (Term.Apply Term.plus n2) (Term.Numeral 0)))) (Term.Apply (Term.Apply Term.neg m1) n2))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_concat1 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, s2, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply (Term.Apply Term.plus __eo_lv_n1_3) (Term.Apply (Term.Apply Term.plus __eo_lv_m1_2) (Term.Numeral 0))))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq m1 __eo_lv_m1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply Term.str_concat s1) s2)) n1) m1)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_concat2 : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | s1, s2, s3, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_s1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3))) n1) m1)) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3))) (Term.Apply (Term.Apply Term.neg n1) (Term.Apply Term.str_len s1))) m1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_replace : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, r1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Apply Term.str_len __eo_lv_r1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_3)) (Term.Numeral 1))) => (__eo_requires (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq r1 __eo_lv_r1_2)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply (Term.Apply Term.str_replace s1) t1) r1)) (Term.Numeral 0)) n1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Numeral 0)) n1)) t1) r1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_full : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_s1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Numeral 0)) n1)) s1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_full_eq : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) __eo_lv_n1_2)) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq n1 __eo_lv_n1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) (Term.Numeral 0)) n1)) s1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_refl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x1) x1)) (Term.Boolean true))


partial def __eo_prog_str_contains_concat_find : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, z1, y1, zs1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_z1_2) __eo_lv_y1_2)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq z1 __eo_lv_z1_2) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.str_contains (__eo_list_concat Term.str_concat xs1 (Term.Apply (Term.Apply Term.str_concat z1) zs1))) y1)) (Term.Boolean true)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_concat_find_contra : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | xs1, z1, y1, zs1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (Term.Apply Term.str_contains y1) (__eo_list_concat Term.str_concat xs1 (Term.Apply (Term.Apply Term.str_concat z1) zs1)))) (Term.Boolean false)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_split_char : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_w1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq w1 __eo_lv_w1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply Term.str_concat x1) (Term.Apply (Term.Apply Term.str_concat y1) z1))) w1)) (__eo_mk_apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains x1) w1)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (__eo_mk_apply Term.str_contains (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat y1) z1))) w1)) (Term.Boolean false)))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_leq_len_eq : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_y1_2)) (Term.Apply Term.str_len __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x1) y1)) (Term.Apply (Term.Apply Term.eq x1) y1)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_emp : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_y1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq y1 __eo_lv_y1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x1) y1)) (Term.Boolean true)))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_char : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_x1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq x1 __eo_lv_x1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x1) y1)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (__eo_mk_apply Term.eq (__seq_empty (Term.Apply Term.Seq _at_T0))) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Boolean false)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_at_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_at x1) n1)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) (Term.Numeral 1)))


partial def __eo_prog_str_replace_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) t1) s1)) s1)


partial def __eo_prog_str_replace_id : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) s1) s1)) t1)


partial def __eo_prog_str_replace_prefix : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t1, t2, r1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply Term.str_concat t1) (Term.Apply (Term.Apply Term.str_concat t2) r1))) t1) s1)) (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat t2) r1)))


partial def __eo_prog_str_replace_no_contains : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_t1_2) __eo_lv_s1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) s1) r1)) t1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_find_base : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | t1, s1, r1, tpre1, tpost1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_2) __eo_lv_s1_2) (Term.Numeral 0))) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpre1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_3) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_4) __eo_lv_s1_3) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpost1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_5) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_6) __eo_lv_s1_4) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len __eo_lv_s1_5)) (Term.Numeral 0)))) (Term.Apply Term.str_len __eo_lv_t1_7)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq tpre1 __eo_lv_tpre1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq t1 __eo_lv_t1_4)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq tpost1 __eo_lv_tpost1_2)) (__eo_eq t1 __eo_lv_t1_5)) (__eo_eq t1 __eo_lv_t1_6)) (__eo_eq s1 __eo_lv_s1_4)) (__eo_eq s1 __eo_lv_s1_5)) (__eo_eq t1 __eo_lv_t1_7)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) s1) r1)) (__eo_mk_apply (Term.Apply Term.str_concat tpre1) (__eo_mk_apply (Term.Apply Term.str_concat r1) (__eo_mk_apply (Term.Apply Term.str_concat tpost1) (__eo_nil Term.str_concat (__eo_typeof tpre1)))))))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_find_first_concat : Term -> Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | t1, ts1, s1, r1, tpre1, tpost1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_2) __eo_lv_s1_2) (Term.Numeral 0))) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpre1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_3) (Term.Numeral 0)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_4) __eo_lv_s1_3) (Term.Numeral 0))))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_tpost1_2) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_5) (Term.Apply (Term.Apply Term.plus (Term.Apply (Term.Apply (Term.Apply Term.str_indexof __eo_lv_t1_6) __eo_lv_s1_4) (Term.Numeral 0))) (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len __eo_lv_s1_5)) (Term.Numeral 0)))) (Term.Apply Term.str_len __eo_lv_t1_7)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq tpre1 __eo_lv_tpre1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq t1 __eo_lv_t1_4)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq tpost1 __eo_lv_tpost1_2)) (__eo_eq t1 __eo_lv_t1_5)) (__eo_eq t1 __eo_lv_t1_6)) (__eo_eq s1 __eo_lv_s1_4)) (__eo_eq s1 __eo_lv_s1_5)) (__eo_eq t1 __eo_lv_t1_7)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply Term.str_concat t1) ts1)) s1) r1)) (Term.Apply (Term.Apply Term.str_concat tpre1) (Term.Apply (Term.Apply Term.str_concat r1) (Term.Apply (Term.Apply Term.str_concat tpost1) ts1)))))
  | _, _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_empty : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_r1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq r1 __eo_lv_r1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) r1) s1)) (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof s1))))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_one_pre : Term -> Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, ts1, ss1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_replace (__eo_list_concat Term.str_concat ts1 (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_list_concat Term.str_concat ss1 (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof ts1))))))) s1) r1)) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_replace (__eo_list_singleton_elim Term.str_concat (__eo_list_concat Term.str_concat ts1 (Term.Apply (Term.Apply Term.str_concat t1) ss1)))) s1) r1)) (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_replace (__eo_list_singleton_elim Term.str_concat (__eo_list_concat Term.str_concat ts1 (Term.Apply (Term.Apply Term.str_concat t1) ss1)))) s1) r1)))))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_find_pre : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t1, r1, ts1, ss1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_replace (__eo_list_concat Term.str_concat ts1 (Term.Apply (Term.Apply Term.str_concat t1) ss1))) t1) r1)) (__eo_list_singleton_elim Term.str_concat (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_replace (__eo_list_singleton_elim Term.str_concat (__eo_list_concat Term.str_concat ts1 (__eo_mk_apply (Term.Apply Term.str_concat t1) (__eo_nil Term.str_concat (__eo_typeof ts1)))))) t1) r1)) ss1)))


partial def __eo_prog_str_replace_all_no_contains : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_t1_2) __eo_lv_s1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t1) s1) r1)) t1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_all_empty : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t1) s1) r1)) t1))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_all_id : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t1) s1) s1)) t1)


partial def __eo_prog_str_replace_all_self : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all t1) t1) s1)) s1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_re_none : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re t1) Term.re_none) r1)) t1)


partial def __eo_prog_str_replace_re_all_none : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all t1) Term.re_none) r1)) t1)


partial def __eo_prog_str_len_concat_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (__eo_mk_apply (Term.Apply Term.plus (Term.Apply Term.str_len s1)) (__eo_mk_apply (__eo_mk_apply Term.plus (__eo_mk_apply Term.str_len (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Numeral 0))))


partial def __eo_prog_str_len_eq_zero_concat_rec : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3, (Term.Apply Term.Seq _at_T0) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.eq s1) (__seq_empty (Term.Apply Term.Seq _at_T0)))) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.str_len (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Numeral 0))) (Term.Boolean true))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_len_eq_zero_base : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s1, (Term.Apply Term.Seq _at_T0) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s1)) (Term.Numeral 0))) (__eo_mk_apply (Term.Apply Term.eq s1) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _ => Term.Stuck


partial def __eo_prog_str_indexof_self : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | t1, n1, (Term.Apply Term.Seq _at_T0) => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) t1) n1)) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_indexof (__seq_empty (Term.Apply Term.Seq _at_T0))) (__seq_empty (Term.Apply Term.Seq _at_T0))) n1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_no_contains : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_2) __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_t1_3))) __eo_lv_s1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) s1) n1)) (Term.Numeral (-1 : eo_lit_Int))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_oob : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_t1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq t1 __eo_lv_t1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) s1) n1)) (Term.Numeral (-1 : eo_lit_Int))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_oob2 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Numeral 0)) __eo_lv_n1_2)) (Term.Boolean true))) => (__eo_requires (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) s1) n1)) (Term.Numeral (-1 : eo_lit_Int))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_contains_pre : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | t1, t2, s1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 0))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_2) __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_t1_3))) __eo_lv_s1_3)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s1 __eo_lv_s1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof (Term.Apply (Term.Apply Term.str_concat t1) t2)) s1) n1)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) s1) n1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_contains_concat_pre : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | t1, t2, t3, s1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_indexof (__eo_list_concat Term.str_concat t1 (Term.Apply (Term.Apply Term.str_concat t2) (Term.Apply (Term.Apply Term.str_concat s1) t3)))) t2) (Term.Numeral 0))) (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_indexof (__eo_list_singleton_elim Term.str_concat (__eo_list_concat Term.str_concat t1 (__eo_mk_apply (Term.Apply Term.str_concat t2) (__eo_nil Term.str_concat (__eo_typeof t1)))))) t2) (Term.Numeral 0)))


partial def __eo_prog_str_indexof_find_emp : Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | t1, emp1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_t1_2)) __eo_lv_n1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_3) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq emp1 __eo_lv_emp1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq n1 __eo_lv_n1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) emp1) n1)) n1))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_eq_irr : Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | t1, s1, r1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_t1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.leq __eo_lv_n1_3) (Term.Apply Term.str_len __eo_lv_r1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_t1_3) __eo_lv_n1_4) (Term.Apply Term.str_len __eo_lv_t1_4))) (Term.Apply (Term.Apply (Term.Apply Term.str_substr __eo_lv_r1_3) __eo_lv_n1_5) (Term.Apply Term.str_len __eo_lv_r1_4)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_3)) (__eo_eq r1 __eo_lv_r1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq n1 __eo_lv_n1_4)) (__eo_eq t1 __eo_lv_t1_4)) (__eo_eq r1 __eo_lv_r1_3)) (__eo_eq n1 __eo_lv_n1_5)) (__eo_eq r1 __eo_lv_r1_4)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof t1) s1) n1)) (Term.Apply (Term.Apply (Term.Apply Term.str_indexof r1) s1) n1))) (Term.Boolean true)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_indexof_re_none : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t1) Term.re_none) n1)) (Term.Numeral (-1 : eo_lit_Int)))


partial def __eo_prog_str_indexof_re_emp_re : Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | t1, r1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.String "")) __eo_lv_r1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_t1_2)) __eo_lv_n1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_3) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq r1 __eo_lv_r1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq n1 __eo_lv_n1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re t1) r1) n1)) n1))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_to_lower_concat : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.str_to_lower (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.str_to_lower s1)) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply Term.str_to_lower (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.String ""))))


partial def __eo_prog_str_to_upper_concat : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s1, s2, s3 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply Term.str_to_upper (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.str_to_upper s1)) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply Term.str_to_upper (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.String ""))))


partial def __eo_prog_str_to_lower_upper : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_lower (Term.Apply Term.str_to_upper s1))) (Term.Apply Term.str_to_lower s1))


partial def __eo_prog_str_to_upper_lower : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_upper (Term.Apply Term.str_to_lower s1))) (Term.Apply Term.str_to_upper s1))


partial def __eo_prog_str_to_lower_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply Term.str_to_lower s1))) (Term.Apply Term.str_len s1))


partial def __eo_prog_str_to_upper_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply Term.str_to_upper s1))) (Term.Apply Term.str_len s1))


partial def __eo_prog_str_to_lower_from_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_lower (Term.Apply Term.str_from_int n1))) (Term.Apply Term.str_from_int n1))


partial def __eo_prog_str_to_upper_from_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_upper (Term.Apply Term.str_from_int n1))) (Term.Apply Term.str_from_int n1))


partial def __eo_prog_str_to_int_concat_neg_one : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, s2, s3, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_int __eo_lv_s2_2)) (Term.Numeral (-1 : eo_lit_Int)))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s2_3)) (Term.Numeral 0))) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq s2 __eo_lv_s2_2) (__eo_eq s2 __eo_lv_s2_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.str_to_int (__eo_list_concat Term.str_concat s1 (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Numeral (-1 : eo_lit_Int))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_is_digit_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_is_digit s1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Numeral 48)) (Term.Apply Term.str_to_code s1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_to_code s1)) (Term.Numeral 57))) (Term.Boolean true))))


partial def __eo_prog_str_leq_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq (Term.String "")) s1)) (Term.Boolean true))


partial def __eo_prog_str_leq_empty_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq s1) (Term.String ""))) (Term.Apply (Term.Apply Term.eq s1) (Term.String "")))


partial def __eo_prog_str_leq_concat_false : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, s2, t2, s3, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Apply Term.str_len __eo_lv_s2_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq __eo_lv_t1_3) __eo_lv_s2_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s2 __eo_lv_s2_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s2 __eo_lv_s2_3)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.str_leq (__eo_list_concat Term.str_concat s1 (Term.Apply (Term.Apply Term.str_concat t1) t2))) (__eo_list_concat Term.str_concat s1 (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Boolean false)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_leq_concat_true : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, t1, s2, t2, s3, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Apply Term.str_len __eo_lv_s2_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_t1_3) __eo_lv_s2_3)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq __eo_lv_t1_4) __eo_lv_s2_4)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s2 __eo_lv_s2_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s2 __eo_lv_s2_3)) (__eo_eq t1 __eo_lv_t1_4)) (__eo_eq s2 __eo_lv_s2_4)) (Term.Boolean true) (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply (__eo_mk_apply Term.str_leq (__eo_list_concat Term.str_concat s1 (Term.Apply (Term.Apply Term.str_concat t1) t2))) (__eo_list_concat Term.str_concat s1 (Term.Apply (Term.Apply Term.str_concat s2) s3)))) (Term.Boolean true)))
  | _, _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_leq_concat_base_1 : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | t1, t2, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Apply Term.str_len __eo_lv_s1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_t1_3) __eo_lv_s1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s1 __eo_lv_s1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq (Term.Apply (Term.Apply Term.str_concat t1) t2)) s1)) (Term.Apply (Term.Apply Term.str_leq t1) s1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_leq_concat_base_2 : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | t1, s1, s2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Apply Term.str_len __eo_lv_s1_2))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_t1_3) __eo_lv_s1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s1 __eo_lv_s1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_leq t1) (Term.Apply (Term.Apply Term.str_concat s1) s2))) (Term.Apply (Term.Apply Term.str_leq t1) s1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_lt_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s1, t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_lt s1) t1)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq s1) t1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_leq s1) t1)) (Term.Boolean true))))


partial def __eo_prog_str_from_int_no_ctn_nondigit : Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | n1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) (Term.String ""))) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_to_int __eo_lv_s1_3)) (Term.Numeral (-1 : eo_lit_Int)))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq s1 __eo_lv_s1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply Term.str_from_int n1)) s1)) (Term.Boolean false)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_ctn_contra : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_t1_2) __eo_lv_s1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_substr t1) n1) m1)) s1)) (Term.Boolean false)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_ctn : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | s1, n1, m1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s1) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1))) (Term.Boolean true))


partial def __eo_prog_str_replace_dual_ctn : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, r1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_s1_2) __eo_lv_u1_2)) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_r1_2) __eo_lv_u1_3)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq u1 __eo_lv_u1_2)) (__eo_eq r1 __eo_lv_r1_2)) (__eo_eq u1 __eo_lv_u1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_replace s1) t1) r1)) u1)) (Term.Boolean true)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_dual_ctn_false : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, t1, r1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_s1_2) __eo_lv_t1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_s1_3) __eo_lv_u1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq u1 __eo_lv_u1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) r1) u1))) (Term.Boolean false)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_replace_self_ctn_simp : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | s1, t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace t1) s1) t1))) (Term.Apply (Term.Apply Term.str_contains s1) t1))


partial def __eo_prog_str_replace_emp_ctn_src : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, emp1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq emp1 __eo_lv_emp1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace emp1) s1) t1))) (Term.Apply (Term.Apply Term.eq emp1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace emp1) s1) t1))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_char_start_eq_len : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, (Term.Apply Term.Seq _at_T0), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Numeral 1)) (Term.Apply Term.str_len __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_eq x1 __eo_lv_x1_2) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) n1) n1)) (__seq_empty (Term.Apply Term.Seq _at_T0))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_repl_char : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_w1_2)) (Term.Numeral 1))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_w1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq y1 __eo_lv_y1_2)) (__eo_eq w1 __eo_lv_w1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) w1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains x1) w1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_contains x1) y1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_contains z1) w1)) (Term.Boolean true)))) (Term.Boolean false)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_repl_self_tgt_char : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_w1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq w1 __eo_lv_w1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) w1)) (Term.Apply (Term.Apply Term.str_contains x1) w1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_contains_repl_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) y1)) (Term.Apply (Term.Apply Term.str_contains x1) y1))


partial def __eo_prog_str_contains_repl_tgt : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) z1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains x1) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_contains x1) z1)) (Term.Boolean false))))


partial def __eo_prog_str_repl_repl_len_id : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_y1_2)) (Term.Apply Term.str_len __eo_lv_x1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) x1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_src_tgt_no_ctn : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_z1_2) __eo_lv_w1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq z1 __eo_lv_z1_2) (__eo_eq w1 __eo_lv_w1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) w1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace z1) x1) y1))) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) w1) z1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_tgt_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) x1) y1))) x1)


partial def __eo_prog_str_repl_repl_tgt_no_ctn : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_x1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) z1) w1))) x1))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_src_self : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) x1) y1)) z1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1))


partial def __eo_prog_str_repl_repl_src_inv_no_ctn1 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) x1) z1)) y1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) y1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_src_inv_no_ctn2 : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) x1) z1)) x1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_src_inv_no_ctn3 : Term -> Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, z1, w1, u1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_x1_2) __eo_lv_z1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_x1_3) __eo_lv_w1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq x1 __eo_lv_x1_3)) (__eo_eq w1 __eo_lv_w1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) z1) w1)) u1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) u1)))
  | _, _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_dual_self : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) x1)) x1)


partial def __eo_prog_str_repl_repl_dual_ite1 : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_x1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq x1 __eo_lv_x1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) w1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.str_contains x1) y1)) x1) w1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_dual_ite2 : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_y1_2) __eo_lv_z1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains __eo_lv_z1_3) __eo_lv_y1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq z1 __eo_lv_z1_3)) (__eo_eq y1 __eo_lv_y1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) w1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.str_contains x1) y1)) x1) w1)))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_repl_repl_lookahead_id_simp : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | y1, z1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) __eo_lv_z1_2)) (Term.Boolean false))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_w1_3)) (Term.Apply Term.str_len __eo_lv_z1_3))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq w1 __eo_lv_w1_3)) (__eo_eq z1 __eo_lv_z1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) w1) y1)) y1) z1)) (Term.Apply (Term.Apply (Term.Apply Term.str_replace (Term.Apply (Term.Apply (Term.Apply Term.str_replace y1) w1) z1)) y1) z1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_re_opt_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_opt x1)) (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.str_to_re (Term.String ""))) (Term.Apply (Term.Apply Term.re_union x1) Term.re_none)))


partial def __eo_prog_re_diff_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_diff x1) y1)) (Term.Apply (Term.Apply Term.re_inter x1) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_comp y1)) Term.re_all)))


partial def __eo_prog_re_plus_elim : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_plus x1)) (Term.Apply (Term.Apply Term.re_concat x1) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult x1)) (Term.Apply Term.str_to_re (Term.String "")))))


partial def __eo_prog_re_repeat_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | n1, x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_exp n1) x1)) (Term.Apply (Term.Apply (Term.Apply Term.re_loop n1) n1) x1))


partial def __eo_prog_re_concat_star_swap : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | xs1, r1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) (Term.Apply (Term.Apply Term.re_concat r1) ys1)))) (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat r1) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) ys1))))


partial def __eo_prog_re_concat_star_repeat : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | xs1, r1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) ys1)))) (__eo_list_singleton_elim Term.re_concat (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) ys1))))


partial def __eo_prog_re_concat_star_subsume1 : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | xs1, r1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) ys1)))) (__eo_list_singleton_elim Term.re_concat (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) ys1))))


partial def __eo_prog_re_concat_star_subsume2 : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | xs1, r1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult r1)) ys1)))) (__eo_list_singleton_elim Term.re_concat (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) ys1))))


partial def __eo_prog_re_concat_merge : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | xs1, s1, t1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re t1)) ys1)))) (__eo_list_singleton_elim Term.re_concat (__eo_list_concat Term.re_concat xs1 (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat t1) (Term.String ""))))) ys1))))


partial def __eo_prog_re_union_all : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | xs1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_union xs1 (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.re_mult Term.re_allchar)) ys1))) (Term.Apply Term.re_mult Term.re_allchar))


partial def __eo_prog_re_union_const_elim : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | r1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re __eo_lv_s1_2) __eo_lv_r1_2)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_union r1) Term.re_none))) r1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_re_inter_all : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | xs1, ys1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_list_concat Term.re_inter xs1 (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.re_mult Term.re_allchar)) ys1))) (__eo_list_singleton_elim Term.re_inter (__eo_list_concat Term.re_inter xs1 ys1)))


partial def __eo_prog_re_star_star : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult (Term.Apply Term.re_mult x1))) (Term.Apply Term.re_mult x1))


partial def __eo_prog_re_range_refl : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_range s1) s1)) (Term.Apply Term.str_to_re s1)))
  | _, _ => Term.Stuck


partial def __eo_prog_re_range_emp : Term -> Term -> Proof -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 1))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Numeral 1))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt (Term.Apply Term.str_to_code __eo_lv_t1_3)) (Term.Apply Term.str_to_code __eo_lv_s1_3))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq t1 __eo_lv_t1_3)) (__eo_eq s1 __eo_lv_s1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_range s1) t1)) Term.re_none))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_re_range_non_singleton_1 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Numeral 1))) (Term.Boolean false))) => (__eo_requires (__eo_eq s1 __eo_lv_s1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_range s1) t1)) Term.re_none))
  | _, _, _ => Term.Stuck


partial def __eo_prog_re_range_non_singleton_2 : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | s1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_t1_2)) (Term.Numeral 1))) (Term.Boolean false))) => (__eo_requires (__eo_eq t1 __eo_lv_t1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_range s1) t1)) Term.re_none))
  | _, _, _ => Term.Stuck


partial def __eo_prog_re_star_union_char : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.re_mult (__eo_list_concat Term.re_union x1 (Term.Apply (Term.Apply Term.re_union Term.re_allchar) y1)))) (Term.Apply Term.re_mult Term.re_allchar))


partial def __eo_prog_re_star_union_drop_emp : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.re_mult (__eo_list_concat Term.re_union x1 (Term.Apply (Term.Apply Term.re_union (Term.Apply Term.str_to_re (Term.String ""))) y1)))) (__eo_mk_apply Term.re_mult (__eo_list_singleton_elim Term.re_union (__eo_list_concat Term.re_union x1 y1))))


partial def __eo_prog_re_loop_neg : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | n1, m1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_n1_2) __eo_lv_m1_2)) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq m1 __eo_lv_m1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.re_loop n1) m1) r1)) Term.re_none))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_re_inter_cstring : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, ys1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re __eo_lv_s1_2) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.str_to_re __eo_lv_s1_3)) (Term.Apply (Term.Apply Term.re_inter __eo_lv_x1_2) __eo_lv_ys1_2)))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq ys1 __eo_lv_ys1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_inter x1) ys1))) (Term.Apply Term.str_to_re s1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_re_inter_cstring_neg : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, ys1, s1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re __eo_lv_s1_2) (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.str_to_re __eo_lv_s1_3)) (Term.Apply (Term.Apply Term.re_inter __eo_lv_x1_2) __eo_lv_ys1_2)))) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq s1 __eo_lv_s1_3)) (__eo_eq x1 __eo_lv_x1_2)) (__eo_eq ys1 __eo_lv_ys1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_inter (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_inter x1) ys1))) Term.re_none))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_len_include : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | s1, s2, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.str_len __eo_lv_s1_2)) (Term.Apply (Term.Apply Term.plus __eo_lv_n1_2) (Term.Apply (Term.Apply Term.plus __eo_lv_m1_2) (Term.Numeral 0))))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq m1 __eo_lv_m1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply Term.str_concat s1) s2)) n1) m1)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_len_include_pre : Term -> Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | s1, s2, s3, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Apply Term.str_len __eo_lv_s1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq n1 __eo_lv_n1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr (Term.Apply (Term.Apply Term.str_concat s1) (Term.Apply (Term.Apply Term.str_concat s2) s3))) (Term.Numeral 0)) n1)) (__eo_mk_apply (Term.Apply Term.str_concat s1) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply (__eo_mk_apply (__eo_mk_apply Term.str_substr (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat s2) s3))) (Term.Numeral 0)) (Term.Apply (Term.Apply Term.neg n1) (Term.Apply Term.str_len s1)))) (__eo_nil Term.str_concat (__eo_typeof s1))))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_substr_len_norm : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | s1, n1, m1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_m1_2) (Term.Apply Term.str_len __eo_lv_s1_2))) (Term.Boolean true))) => (__eo_requires (__eo_and (__eo_eq m1 __eo_lv_m1_2) (__eo_eq s1 __eo_lv_s1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) m1)) (Term.Apply (Term.Apply (Term.Apply Term.str_substr s1) n1) (Term.Apply Term.str_len s1))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_seq_len_rev : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply Term.str_rev x1))) (Term.Apply Term.str_len x1))


partial def __eo_prog_seq_rev_rev : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_rev (Term.Apply Term.str_rev x1))) x1)


partial def __eo_prog_seq_rev_concat : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | x1, y1, z1 => (__eo_mk_apply (__eo_mk_apply Term.eq (__eo_mk_apply Term.str_rev (__eo_mk_apply (Term.Apply Term.str_concat x1) (__eo_list_concat Term.str_concat y1 (__eo_mk_apply (Term.Apply Term.str_concat z1) (__eo_nil Term.str_concat (__eo_typeof x1))))))) (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.str_rev z1)) (__eo_mk_apply (__eo_mk_apply Term.str_concat (__eo_mk_apply Term.str_rev (__eo_list_singleton_elim Term.str_concat (Term.Apply (Term.Apply Term.str_concat x1) y1)))) (__eo_nil Term.str_concat (__eo_typeof (Term.Apply Term.str_rev z1))))))


partial def __eo_prog_str_eq_repl_self_emp : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, emp1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))) => (__eo_requires (__eo_eq emp1 __eo_lv_emp1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) emp1)) (Term.Apply (Term.Apply Term.eq x1) emp1)))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_no_change : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_y1_2) __eo_lv_z1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) x1)) (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_contains x1) y1))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_tgt_eq_len : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, y1, z1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_y1_2)) (Term.Apply Term.str_len __eo_lv_z1_2))) => (__eo_requires (__eo_and (__eo_eq y1 __eo_lv_y1_2) (__eo_eq z1 __eo_lv_z1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) z1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x1) y1)) (Term.Apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.eq x1) z1)) (Term.Boolean false)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_len_one_emp_prefix : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, emp1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_y1_2)) (Term.Numeral 1))) => (__eo_requires (__eo_and (__eo_eq emp1 __eo_lv_emp1_2) (__eo_eq y1 __eo_lv_y1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) emp1)) emp1)) (Term.Apply (Term.Apply Term.str_prefixof x1) y1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_emp_tgt_nemp : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, z1, emp1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_z1_2) __eo_lv_emp1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_eq emp1 __eo_lv_emp1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq emp1 __eo_lv_emp1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) z1)) emp1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) emp1)) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq y1) emp1))) (Term.Boolean true)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_nemp_src_emp : Term -> Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | x1, y1, z1, emp1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_emp1_2)) (Term.Numeral 0))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_z1_2) __eo_lv_emp1_3)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_and (__eo_eq emp1 __eo_lv_emp1_2) (__eo_eq z1 __eo_lv_z1_2)) (__eo_eq emp1 __eo_lv_emp1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace emp1) x1) y1)) z1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq x1) emp1)) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq y1) z1)) (Term.Boolean true)))))
  | _, _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_eq_repl_self_src : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, y1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) y1) x1)) y1)) (Term.Apply (Term.Apply Term.eq x1) y1))


partial def __eo_prog_seq_len_unit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len (Term.Apply Term.seq_unit x1))) (Term.Numeral 1))


partial def __eo_prog_seq_nth_unit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.seq_nth (Term.Apply Term.seq_unit x1)) (Term.Numeral 0))) x1)


partial def __eo_prog_seq_rev_unit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_rev (Term.Apply Term.seq_unit x1))) (Term.Apply Term.seq_unit x1))


partial def __eo_prog_re_in_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) Term.re_none)) (Term.Boolean false))


partial def __eo_prog_re_in_sigma : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) Term.re_allchar)) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len t1)) (Term.Numeral 1)))


partial def __eo_prog_re_in_sigma_star : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) (Term.Apply Term.re_mult Term.re_allchar))) (Term.Boolean true))


partial def __eo_prog_re_in_cstring : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) (Term.Apply Term.str_to_re s1))) (Term.Apply (Term.Apply Term.eq t1) s1))


partial def __eo_prog_re_in_comp : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) (Term.Apply Term.re_comp r1))) (Term.Apply Term.not (Term.Apply (Term.Apply Term.str_in_re t1) r1)))


partial def __eo_prog_str_in_re_union_elim : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, r1, r2, rs1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s1) (Term.Apply (Term.Apply Term.re_union r1) (Term.Apply (Term.Apply Term.re_union r2) rs1)))) (__eo_mk_apply (Term.Apply Term.or (Term.Apply (Term.Apply Term.str_in_re s1) r1)) (__eo_mk_apply (__eo_mk_apply Term.or (__eo_mk_apply (Term.Apply Term.str_in_re s1) (__eo_list_singleton_elim Term.re_union (Term.Apply (Term.Apply Term.re_union r2) rs1)))) (Term.Boolean false))))


partial def __eo_prog_str_in_re_inter_elim : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | s1, r1, r2, rs1 => (__eo_mk_apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s1) (Term.Apply (Term.Apply Term.re_inter r1) (Term.Apply (Term.Apply Term.re_inter r2) rs1)))) (__eo_mk_apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_in_re s1) r1)) (__eo_mk_apply (__eo_mk_apply Term.and (__eo_mk_apply (Term.Apply Term.str_in_re s1) (__eo_list_singleton_elim Term.re_inter (Term.Apply (Term.Apply Term.re_inter r2) rs1)))) (Term.Boolean true))))


partial def __eo_prog_str_in_re_range_elim : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | s1, c1, c2, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_c1_2)) (Term.Numeral 1))), (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len __eo_lv_c2_2)) (Term.Numeral 1))) => (__eo_requires (__eo_and (__eo_eq c1 __eo_lv_c1_2) (__eo_eq c2 __eo_lv_c2_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re s1) (Term.Apply (Term.Apply Term.re_range c1) c2))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_to_code c1)) (Term.Apply Term.str_to_code s1))) (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_to_code s1)) (Term.Apply Term.str_to_code c2))) (Term.Boolean true)))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_str_in_re_contains : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re t1) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult Term.re_allchar)) (Term.Apply Term.str_to_re (Term.String ""))))))) (Term.Apply (Term.Apply Term.str_contains t1) s1))


partial def __eo_prog_str_in_re_from_int_nemp_dig_range : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq __eo_lv_n1_2) (Term.Numeral 0))) (Term.Boolean true))) => (__eo_requires (__eo_eq n1 __eo_lv_n1_2) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.Apply Term.str_from_int n1)) (Term.Apply (Term.Apply Term.re_concat (Term.Apply (Term.Apply Term.re_range (Term.String "0")) (Term.String "9"))) (Term.Apply (Term.Apply Term.re_concat (Term.Apply Term.re_mult (Term.Apply (Term.Apply Term.re_range (Term.String "0")) (Term.String "9")))) (Term.Apply Term.str_to_re (Term.String "")))))) (Term.Boolean true)))
  | _, _ => Term.Stuck


partial def __eo_prog_str_in_re_from_int_dig_range : Term -> Term
  | Term.Stuck  => Term.Stuck
  | n1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_in_re (Term.Apply Term.str_from_int n1)) (Term.Apply Term.re_mult (Term.Apply (Term.Apply Term.re_range (Term.String "0")) (Term.String "9"))))) (Term.Boolean true))


partial def __eo_prog_eq_refl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) t1)) (Term.Boolean true))


partial def __eo_prog_eq_symm : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) s1)) (Term.Apply (Term.Apply Term.eq s1) t1))


partial def __eo_prog_eq_cond_deq : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | t1, s1, r1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq __eo_lv_s1_2) __eo_lv_r1_2)) (Term.Boolean false))) => (__eo_requires (__eo_and (__eo_eq s1 __eo_lv_s1_2) (__eo_eq r1 __eo_lv_r1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t1) s1)) (Term.Apply (Term.Apply Term.eq t1) r1))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) s1))) (Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) r1))) (Term.Boolean true)))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_eq_ite_lift : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | C1, t1, s1, r1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.ite C1) t1) s1)) r1)) (Term.Apply (Term.Apply (Term.Apply Term.ite C1) (Term.Apply (Term.Apply Term.eq t1) r1)) (Term.Apply (Term.Apply Term.eq s1) r1)))


partial def __eo_prog_distinct_binary_elim : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct (Term.Apply (Term.Apply Term.__eo_List_cons t1) (Term.Apply (Term.Apply Term.__eo_List_cons s1) Term.__eo_List_nil)))) (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) s1)))


partial def __eo_prog_uf_bv2nat_int2bv : Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | w1, t1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply Term._at_bvsize __eo_lv_t1_2)) __eo_lv_w1_2)) => (__eo_requires (__eo_and (__eo_eq t1 __eo_lv_t1_2) (__eo_eq w1 __eo_lv_w1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.int_to_bv w1) (Term.Apply Term.ubv_to_int t1))) t1))
  | _, _, _ => Term.Stuck


partial def __eo_prog_uf_bv2nat_int2bv_extend : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | w1, t1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.gt __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_t1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_w1_3) (Term.Apply Term._at_bvsize __eo_lv_t1_3)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq w1 __eo_lv_w1_3)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.int_to_bv w1) (Term.Apply Term.ubv_to_int t1))) (Term.Apply (Term.Apply Term.concat (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) n1)) (Term.Apply (Term.Apply Term.concat t1) (Term.Binary 0 0)))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_uf_bv2nat_int2bv_extract : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | w1, t1, wm1, (Proof.pf (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.lt __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_t1_2))) (Term.Boolean true))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg __eo_lv_w1_3) (Term.Numeral 1)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq wm1 __eo_lv_wm1_2)) (__eo_eq w1 __eo_lv_w1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.int_to_bv w1) (Term.Apply Term.ubv_to_int t1))) (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) (Term.Numeral 0)) t1)))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_prog_uf_int2bv_bv2nat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | w1, t1 => (Term.Apply (Term.Apply Term.eq (Term.Apply Term.ubv_to_int (Term.Apply (Term.Apply Term.int_to_bv w1) t1))) (Term.Apply (Term.Apply Term.mod_total t1) (Term.Apply Term.int_pow2 w1)))


partial def __eo_prog_uf_bv2nat_geq_elim : Term -> Term -> Term -> Proof -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | x1, n1, w1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_w1_2) (Term.Apply Term._at_bvsize __eo_lv_x1_2))) => (__eo_requires (__eo_and (__eo_eq w1 __eo_lv_w1_2) (__eo_eq x1 __eo_lv_x1_2)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.geq (Term.Apply Term.ubv_to_int x1)) n1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.geq n1) (Term.Apply Term.int_pow2 w1))) (Term.Boolean false)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.lt n1) (Term.Numeral 0))) (Term.Boolean true)) (Term.Apply (Term.Apply Term.bvuge x1) (Term.Apply (Term.Apply Term.int_to_bv w1) n1))))))
  | _, _, _, _ => Term.Stuck


partial def __eo_prog_uf_int2bv_bvult_equiv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvult t1) s1)) (Term.Apply (Term.Apply Term.lt (Term.Apply Term.ubv_to_int t1)) (Term.Apply Term.ubv_to_int s1)))


partial def __eo_prog_uf_int2bv_bvule_equiv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t1, s1 => (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.bvule t1) s1)) (Term.Apply (Term.Apply Term.leq (Term.Apply Term.ubv_to_int t1)) (Term.Apply Term.ubv_to_int s1)))


partial def __eo_prog_uf_sbv_to_int_elim : Term -> Term -> Term -> Proof -> Proof -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | t1, wm1, n1, (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_wm1_2) (Term.Apply (Term.Apply Term.neg (Term.Apply Term._at_bvsize __eo_lv_t1_2)) (Term.Numeral 1)))), (Proof.pf (Term.Apply (Term.Apply Term.eq __eo_lv_n1_2) (Term.Apply Term.int_pow2 (Term.Apply Term._at_bvsize __eo_lv_t1_3)))) => (__eo_requires (__eo_and (__eo_and (__eo_and (__eo_eq wm1 __eo_lv_wm1_2) (__eo_eq t1 __eo_lv_t1_2)) (__eo_eq n1 __eo_lv_n1_2)) (__eo_eq t1 __eo_lv_t1_3)) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.sbv_to_int t1)) (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply (Term.Apply Term.extract wm1) wm1) t1)) (Term.Apply (Term.Apply Term._at_bv (Term.Numeral 0)) (Term.Numeral 1)))) (Term.Apply Term.ubv_to_int t1)) (Term.Apply (Term.Apply Term.neg (Term.Apply Term.ubv_to_int t1)) n1))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_l_2___get_ai_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, x => (__eo_cons f x id)


partial def __eo_l_1___get_ai_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, __eo_lv_id_2 => (__eo_ite (__eo_eq id __eo_lv_id_2) id (__eo_l_2___get_ai_norm_rec f id __eo_lv_id_2))


partial def __get_ai_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_list_setof f (__eo_list_concat f (__get_ai_norm_rec f id x1) (__get_ai_norm_rec f id x2))) (__eo_l_1___get_ai_norm_rec f id (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___get_ai_norm_rec __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __get_ai_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y) => (__eo_list_singleton_elim f (__get_ai_norm_rec f (__eo_nil f (__eo_typeof (Term.Apply (Term.Apply f x) y))) (Term.Apply (Term.Apply f x) y)))
  | _ => Term.Stuck


partial def __eo_l_2___get_a_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, x => (__eo_cons f x id)


partial def __eo_l_1___get_a_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, __eo_lv_id_2 => (__eo_ite (__eo_eq id __eo_lv_id_2) id (__eo_l_2___get_a_norm_rec f id __eo_lv_id_2))


partial def __get_a_norm_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, id, (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_list_concat f (__get_a_norm_rec f id x1) (__get_a_norm_rec f id x2)) (__eo_l_1___get_a_norm_rec f id (Term.Apply (Term.Apply __eo_lv_f_2 x1) x2)))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_1___get_a_norm_rec __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __get_a_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f x) y) => (__eo_list_singleton_elim f (__get_a_norm_rec f (__eo_nil f (__eo_typeof (Term.Apply (Term.Apply f x) y))) (Term.Apply (Term.Apply f x) y)))
  | _ => Term.Stuck


partial def __eo_l_3___aci_norm_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean false)


partial def __eo_l_2___aci_norm_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_aci_sorted f) t), (Term.Apply (Term.Apply Term._at__at_aci_sorted __eo_lv_f_2) s) => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_list_meq f t s) (__eo_l_3___aci_norm_eq (Term.Apply (Term.Apply Term._at__at_aci_sorted f) t) (Term.Apply (Term.Apply Term._at__at_aci_sorted __eo_lv_f_2) s)))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_3___aci_norm_eq __eo_dv_1 __eo_dv_2)


partial def __eo_l_1___aci_norm_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term._at__at_aci_sorted f) t), __eo_lv_t_2 => (__eo_ite (__eo_eq t __eo_lv_t_2) (Term.Boolean true) (__eo_l_2___aci_norm_eq (Term.Apply (Term.Apply Term._at__at_aci_sorted f) t) __eo_lv_t_2))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_2___aci_norm_eq __eo_dv_1 __eo_dv_2)


partial def __aci_norm_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, __eo_lv_t_2 => (__eo_ite (__eo_eq t __eo_lv_t_2) (Term.Boolean true) (__eo_l_1___aci_norm_eq t __eo_lv_t_2))


partial def __run_evaluate : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq x) y) => (__eo_ite (__eo_and (__eo_is_q (__run_evaluate x)) (__eo_is_q (__run_evaluate y))) (__eo_eq (__run_evaluate x) (__run_evaluate y)) (__eo_ite (__eo_and (__eo_is_z (__run_evaluate x)) (__eo_is_z (__run_evaluate y))) (__eo_eq (__run_evaluate x) (__run_evaluate y)) (__eo_ite (__eo_and (__eo_is_bin (__run_evaluate x)) (__eo_is_bin (__run_evaluate y))) (__eo_eq (__run_evaluate x) (__run_evaluate y)) (__eo_ite (__eo_and (__eo_is_str (__run_evaluate x)) (__eo_is_str (__run_evaluate y))) (__eo_eq (__run_evaluate x) (__run_evaluate y)) (__eo_ite (__eo_and (__eo_is_bool (__run_evaluate x)) (__eo_is_bool (__run_evaluate y))) (__eo_eq (__run_evaluate x) (__run_evaluate y)) (__eo_mk_apply (__eo_mk_apply Term.eq (__run_evaluate x)) (__run_evaluate y)))))))
  | (Term.Apply Term.not b) => (__eo_not (__run_evaluate b))
  | (Term.Apply (Term.Apply (Term.Apply Term.ite b) x) y) => (__eo_ite (__run_evaluate b) (__run_evaluate x) (__run_evaluate y))
  | (Term.Apply (Term.Apply Term.or b) bs) => (__eo_or (__run_evaluate b) (__run_evaluate bs))
  | (Term.Apply (Term.Apply Term.imp b) b2) => (__eo_or (__eo_not (__run_evaluate b)) (__run_evaluate b2))
  | (Term.Apply (Term.Apply Term.and b) bs) => (__eo_and (__run_evaluate b) (__run_evaluate bs))
  | (Term.Apply (Term.Apply Term.xor b) b2) => (__eo_xor (__run_evaluate b) (__run_evaluate b2))
  | (Term.Apply (Term.Apply Term.lt x) z) => (__eo_is_neg (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_neg (__eo_to_q (__run_evaluate z)))))
  | (Term.Apply (Term.Apply Term.leq x) z) => (__eo_or (__eo_is_neg (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_neg (__eo_to_q (__run_evaluate z))))) (__eo_eq (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_neg (__eo_to_q (__run_evaluate z)))) (Term.Rational (eo_lit_mk_rational 0 1))))
  | (Term.Apply (Term.Apply Term.gt x) z) => (__eo_is_neg (__eo_add (__eo_to_q (__run_evaluate z)) (__eo_neg (__eo_to_q (__run_evaluate x)))))
  | (Term.Apply (Term.Apply Term.geq x) z) => (__eo_or (__eo_is_neg (__eo_add (__eo_to_q (__run_evaluate z)) (__eo_neg (__eo_to_q (__run_evaluate x))))) (__eo_eq (__eo_add (__eo_to_q (__run_evaluate z)) (__eo_neg (__eo_to_q (__run_evaluate x)))) (Term.Rational (eo_lit_mk_rational 0 1))))
  | (Term.Apply (Term.Apply Term.plus x) ys) => (__eo_ite (__eo_eq (__run_evaluate x) (__eo_to_q (__run_evaluate x))) (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate ys))) (__eo_ite (__eo_eq (__run_evaluate ys) (__eo_to_q (__run_evaluate ys))) (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate ys))) (__eo_add (__run_evaluate x) (__run_evaluate ys))))
  | (Term.Apply (Term.Apply Term.neg x) z) => (__eo_ite (__eo_eq (__run_evaluate x) (__eo_to_q (__run_evaluate x))) (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_to_q (__eo_neg (__run_evaluate z)))) (__eo_ite (__eo_eq (__eo_neg (__run_evaluate z)) (__eo_to_q (__eo_neg (__run_evaluate z)))) (__eo_add (__eo_to_q (__run_evaluate x)) (__eo_to_q (__eo_neg (__run_evaluate z)))) (__eo_add (__run_evaluate x) (__eo_neg (__run_evaluate z)))))
  | (Term.Apply (Term.Apply Term.mult x) ys) => (__eo_ite (__eo_eq (__run_evaluate x) (__eo_to_q (__run_evaluate x))) (__eo_mul (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate ys))) (__eo_ite (__eo_eq (__run_evaluate ys) (__eo_to_q (__run_evaluate ys))) (__eo_mul (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate ys))) (__eo_mul (__run_evaluate x) (__run_evaluate ys))))
  | (Term.Apply Term.__eoo_neg_2 x) => (__eo_neg (__run_evaluate x))
  | (Term.Apply (Term.Apply Term.qdiv x) y) => (__eo_qdiv (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate y)))
  | (Term.Apply (Term.Apply Term.qdiv_total x) y) => (__eo_ite (__eo_eq (__eo_to_q (__run_evaluate y)) (Term.Rational (eo_lit_mk_rational 0 1))) (Term.Rational (eo_lit_mk_rational 0 1)) (__eo_qdiv (__eo_to_q (__run_evaluate x)) (__eo_to_q (__run_evaluate y))))
  | (Term.Apply (Term.Apply Term.div i1) i2) => (__eo_zdiv (__run_evaluate i1) (__run_evaluate i2))
  | (Term.Apply (Term.Apply Term.div_total i1) i2) => (__eo_ite (__eo_eq (__run_evaluate i2) (Term.Numeral 0)) (Term.Numeral 0) (__eo_zdiv (__run_evaluate i1) (__run_evaluate i2)))
  | (Term.Apply (Term.Apply Term.mod i1) i2) => (__eo_zmod (__run_evaluate i1) (__run_evaluate i2))
  | (Term.Apply (Term.Apply Term.mod_total i1) i2) => (__eo_ite (__eo_eq (__run_evaluate i2) (Term.Numeral 0)) (__run_evaluate i1) (__eo_zmod (__run_evaluate i1) (__run_evaluate i2)))
  | (Term.Apply Term.to_real x) => (__eo_to_q (__run_evaluate x))
  | (Term.Apply Term.to_int x) => (__eo_to_z (__run_evaluate x))
  | (Term.Apply Term.is_int x) => (__eo_eq (__eo_to_q (__eo_to_z (__run_evaluate x))) (__eo_to_q (__run_evaluate x)))
  | (Term.Apply Term.abs x) => (__eo_ite (__eo_is_neg (__run_evaluate x)) (__eo_neg (__run_evaluate x)) (__run_evaluate x))
  | (Term.Apply Term.int_log2 i1) => (__eo_ite (__eo_is_neg (__eo_neg (__run_evaluate i1))) (__arith_eval_int_log_2_rec (__run_evaluate i1)) (Term.Numeral 0))
  | (Term.Apply Term.int_pow2 i1) => (__eo_ite (__eo_is_z (__run_evaluate i1)) (__eo_ite (__eo_is_neg (__run_evaluate i1)) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__run_evaluate i1))) (__eo_mk_apply Term.int_pow2 (__run_evaluate i1)))
  | (Term.Apply Term.int_ispow2 i1) => (__eo_ite (__eo_is_z (__run_evaluate i1)) (__eo_ite (__eo_is_neg (__run_evaluate i1)) (Term.Boolean false) (__eo_eq (__run_evaluate i1) (__eo_ite (__eo_is_z (__eo_ite (__eo_is_neg (__eo_neg (__run_evaluate i1))) (__arith_eval_int_log_2_rec (__run_evaluate i1)) (Term.Numeral 0))) (__eo_ite (__eo_is_neg (__eo_ite (__eo_is_neg (__eo_neg (__run_evaluate i1))) (__arith_eval_int_log_2_rec (__run_evaluate i1)) (Term.Numeral 0))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_ite (__eo_is_neg (__eo_neg (__run_evaluate i1))) (__arith_eval_int_log_2_rec (__run_evaluate i1)) (Term.Numeral 0)))) (__eo_mk_apply Term.int_pow2 (__eo_ite (__eo_is_neg (__eo_neg (__run_evaluate i1))) (__arith_eval_int_log_2_rec (__run_evaluate i1)) (Term.Numeral 0)))))) (__eo_mk_apply Term.int_ispow2 (__run_evaluate i1)))
  | (Term.Apply (Term.Apply Term.str_concat sx) sys) => (__eo_concat (__run_evaluate sx) (__run_evaluate sys))
  | (Term.Apply Term.str_len sx) => (__eo_len (__run_evaluate sx))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr sx) n) m) => (__eo_extract (__run_evaluate sx) (__run_evaluate n) (__eo_add (__eo_add (__run_evaluate n) (__run_evaluate m)) (Term.Numeral (-1 : eo_lit_Int))))
  | (Term.Apply (Term.Apply Term.str_at sx) n) => (__eo_extract (__run_evaluate sx) (__run_evaluate n) (__run_evaluate n))
  | (Term.Apply (Term.Apply Term.str_contains sx) sy) => (__eo_not (__eo_is_neg (__eo_find (__run_evaluate sx) (__run_evaluate sy))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace sx) sy) sz) => (__eo_ite (__eo_is_neg (__eo_find (__eo_to_str (__run_evaluate sx)) (__eo_to_str (__run_evaluate sy)))) (__run_evaluate sx) (__eo_concat (__eo_concat (__eo_extract (__run_evaluate sx) (Term.Numeral 0) (__eo_add (__eo_find (__eo_to_str (__run_evaluate sx)) (__eo_to_str (__run_evaluate sy))) (Term.Numeral (-1 : eo_lit_Int)))) (__run_evaluate sz)) (__eo_extract (__run_evaluate sx) (__eo_add (__eo_find (__eo_to_str (__run_evaluate sx)) (__eo_to_str (__run_evaluate sy))) (__eo_len (__run_evaluate sy))) (__eo_len (__run_evaluate sx)))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all ssx) ssy) ssz) => (__eo_ite (__eo_and (__eo_and (__eo_is_str ssx) (__eo_is_str ssy)) (__eo_is_str ssz)) (__eo_ite (__eo_eq ssy (Term.String "")) ssx (__str_eval_replace_all_rec ssx ssy ssz (__eo_find ssx ssy) (__eo_len ssy))) (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all ssx) ssy) ssz))
  | (Term.Apply (Term.Apply Term.str_prefixof sx) sy) => (__eo_eq (__run_evaluate sx) (__eo_extract (__run_evaluate sy) (Term.Numeral 0) (__eo_add (__eo_len (__run_evaluate sx)) (Term.Numeral (-1 : eo_lit_Int)))))
  | (Term.Apply (Term.Apply Term.str_suffixof sx) sy) => (__eo_eq (__run_evaluate sx) (__eo_extract (__run_evaluate sy) (__eo_add (__eo_len (__run_evaluate sy)) (__eo_neg (__eo_len (__run_evaluate sx)))) (__eo_add (__eo_len (__run_evaluate sy)) (Term.Numeral (-1 : eo_lit_Int)))))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof sx) sy) n) => (__eo_ite (__eo_is_neg (__run_evaluate n)) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_gt (__run_evaluate n) (__eo_len (__run_evaluate sx))) (Term.Numeral (-1 : eo_lit_Int)) (__eo_ite (__eo_is_neg (__eo_find (__eo_to_str (__eo_extract (__run_evaluate sx) n (__eo_len (__run_evaluate sx)))) (__eo_to_str (__run_evaluate sy)))) (__eo_find (__eo_to_str (__eo_extract (__run_evaluate sx) n (__eo_len (__run_evaluate sx)))) (__eo_to_str (__run_evaluate sy))) (__eo_add n (__eo_find (__eo_to_str (__eo_extract (__run_evaluate sx) n (__eo_len (__run_evaluate sx)))) (__eo_to_str (__run_evaluate sy)))))))
  | (Term.Apply Term.str_to_code ssx) => (__eo_ite (__eo_eq (__eo_len (__run_evaluate ssx)) (Term.Numeral 1)) (__eo_to_z (__run_evaluate ssx)) (__eo_ite (__eo_is_z (__eo_len (__run_evaluate ssx))) (Term.Numeral (-1 : eo_lit_Int)) (__eo_mk_apply Term.str_to_code (__run_evaluate ssx))))
  | (Term.Apply Term.str_from_code n) => (__eo_ite (__eo_ite (__eo_is_z (__run_evaluate n)) (__eo_ite (__eo_ite (__eo_eq (Term.Numeral 196608) (__run_evaluate n)) (Term.Boolean true) (__eo_gt (Term.Numeral 196608) (__run_evaluate n))) (__eo_not (__eo_is_neg (__run_evaluate n))) (Term.Boolean false)) (Term.Boolean false)) (__eo_to_str n) (Term.String ""))
  | (Term.Apply Term.str_to_int ssx) => (__eo_ite (__eo_is_str (__run_evaluate ssx)) (__eo_ite (__eo_eq (__run_evaluate ssx) (Term.String "")) (Term.Numeral (-1 : eo_lit_Int)) (__str_to_int_eval_rec (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__run_evaluate ssx)))) (Term.Numeral 1) (Term.Numeral 0))) (__eo_mk_apply Term.str_to_int (__run_evaluate ssx)))
  | (Term.Apply Term.str_from_int n) => (__eo_ite (__eo_is_z (__run_evaluate n)) (__eo_ite (__eo_is_neg (__run_evaluate n)) (Term.String "") (__str_from_int_eval_rec (__run_evaluate n) (Term.String ""))) (__eo_mk_apply Term.str_from_int (__run_evaluate n)))
  | (Term.Apply (Term.Apply Term.str_leq ssx) ssy) => (__eo_ite (__eo_and (__eo_is_str (__run_evaluate ssx)) (__eo_is_str (__run_evaluate ssy))) (__str_leq_eval_rec (__str_flatten (__str_nary_intro (__run_evaluate ssx))) (__str_flatten (__str_nary_intro (__run_evaluate ssy)))) (__eo_mk_apply (__eo_mk_apply Term.str_leq (__run_evaluate ssx)) (__run_evaluate ssy)))
  | (Term.Apply Term.str_to_lower ssx) => (__eo_ite (__eo_is_str (__run_evaluate ssx)) (__str_case_conv_rec (__str_flatten (__str_nary_intro (__run_evaluate ssx))) (Term.Boolean true)) (__eo_mk_apply Term.str_to_lower (__run_evaluate ssx)))
  | (Term.Apply Term.str_to_upper ssx) => (__eo_ite (__eo_is_str (__run_evaluate ssx)) (__str_case_conv_rec (__str_flatten (__str_nary_intro (__run_evaluate ssx))) (Term.Boolean false)) (__eo_mk_apply Term.str_to_upper (__run_evaluate ssx)))
  | (Term.Apply Term.str_rev sx) => (__eo_ite (__eo_is_str (__run_evaluate sx)) (__str_nary_elim (__str_collect (__eo_list_rev Term.str_concat (__str_flatten (__str_nary_intro (__run_evaluate sx)))))) (__eo_mk_apply Term.str_rev (__run_evaluate sx)))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_update sx) n) sy) => (__eo_ite (__eo_or (__eo_gt (Term.Numeral 0) (__run_evaluate n)) (__eo_gt (__run_evaluate n) (__eo_len (__run_evaluate sx)))) (__run_evaluate sx) (__eo_concat (__eo_concat (__eo_extract (__run_evaluate sx) (Term.Numeral 0) (__eo_add (__run_evaluate n) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_extract (__run_evaluate sy) (Term.Numeral 0) (__eo_add (__eo_add (__eo_neg (__run_evaluate n)) (__eo_len (__run_evaluate sx))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_extract (__run_evaluate sx) (__eo_add (__run_evaluate n) (__eo_len (__run_evaluate sy))) (__eo_len (__run_evaluate sx)))))
  | (Term.Apply Term.bvnot xb) => (__eo_not (__run_evaluate xb))
  | (Term.Apply Term.bvneg xb) => (__eo_neg (__run_evaluate xb))
  | (Term.Apply (Term.Apply Term.bvadd xb) ybs) => (__eo_add (__run_evaluate xb) (__run_evaluate ybs))
  | (Term.Apply (Term.Apply Term.bvmul xb) ybs) => (__eo_mul (__run_evaluate xb) (__run_evaluate ybs))
  | (Term.Apply (Term.Apply Term.bvudiv xb) yb) => (__eo_ite (__eo_eq (__eo_to_z (__run_evaluate yb)) (Term.Numeral 0)) (__eo_to_bin (__bv_bitwidth (__eo_typeof xb)) (__eo_add (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof xb))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof xb))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__bv_bitwidth (__eo_typeof xb)))) (__eo_mk_apply Term.int_pow2 (__bv_bitwidth (__eo_typeof xb)))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_zdiv (__run_evaluate xb) (__run_evaluate yb)))
  | (Term.Apply (Term.Apply Term.bvurem xb) yb) => (__eo_ite (__eo_eq (__eo_to_z (__run_evaluate yb)) (Term.Numeral 0)) (__run_evaluate xb) (__eo_zmod (__run_evaluate xb) (__run_evaluate yb)))
  | (Term.Apply (Term.Apply Term.bvand xb) ybs) => (__eo_and (__run_evaluate xb) (__run_evaluate ybs))
  | (Term.Apply (Term.Apply Term.bvor xb) ybs) => (__eo_or (__run_evaluate xb) (__run_evaluate ybs))
  | (Term.Apply (Term.Apply Term.bvxor xb) ybs) => (__eo_xor (__run_evaluate xb) (__run_evaluate ybs))
  | (Term.Apply (Term.Apply Term.concat xb) zbs) => (__eo_concat (__run_evaluate xb) (__run_evaluate zbs))
  | (Term.Apply (Term.Apply Term.bvsub xb) yb) => (__eo_add (__run_evaluate xb) (__eo_neg (__run_evaluate yb)))
  | (Term.Apply (Term.Apply (Term.Apply Term.extract m) n) xb) => (__eo_extract (__run_evaluate xb) n m)
  | (Term.Apply (Term.Apply Term.bvult xb) yb) => (__run_evaluate (Term.Apply (Term.Apply Term.bvugt yb) xb))
  | (Term.Apply (Term.Apply Term.bvule xb) yb) => (__run_evaluate (Term.Apply (Term.Apply Term.bvuge yb) xb))
  | (Term.Apply (Term.Apply Term.bvugt xb) yb) => (__eo_gt (__eo_to_z (__run_evaluate xb)) (__eo_to_z (__run_evaluate yb)))
  | (Term.Apply (Term.Apply Term.bvuge xb) yb) => (__eo_or (__eo_gt (__run_evaluate xb) (__run_evaluate yb)) (__eo_eq (__run_evaluate xb) (__run_evaluate yb)))
  | (Term.Apply (Term.Apply Term.bvslt xb) yb) => (__run_evaluate (Term.Apply (Term.Apply Term.bvsgt yb) xb))
  | (Term.Apply (Term.Apply Term.bvsle xb) yb) => (__run_evaluate (Term.Apply (Term.Apply Term.bvsge yb) xb))
  | (Term.Apply (Term.Apply Term.bvsgt xb) yb) => (__eo_gt (__eo_ite (__eo_eq (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_ite (__eo_eq (__eo_extract (__run_evaluate yb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int)))))))
  | (Term.Apply (Term.Apply Term.bvsge xb) yb) => (__eo_or (__eo_gt (__eo_ite (__eo_eq (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_ite (__eo_eq (__eo_extract (__run_evaluate yb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int))))))) (__eo_eq (__eo_ite (__eo_eq (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate xb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_ite (__eo_eq (__eo_extract (__run_evaluate yb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 1)) (__eo_add (__eo_neg (__eo_ite (__eo_is_z (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (__eo_ite (__eo_is_neg (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply Term.int_pow2 (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-1 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int)))))) (__eo_to_z (__eo_extract (__run_evaluate yb) (Term.Numeral 0) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate yb))) (Term.Numeral (-2 : eo_lit_Int))))))))
  | (Term.Apply (Term.Apply Term.bvshl xb) yb) => (__eo_ite (__eo_gt (__eo_to_z (__run_evaluate yb)) (__bv_bitwidth (__eo_typeof xb))) (__eo_to_bin (__bv_bitwidth (__eo_typeof xb)) (Term.Numeral 0)) (__eo_to_bin (__bv_bitwidth (__eo_typeof xb)) (__eo_mul (__eo_to_z (__run_evaluate xb)) (__eo_ite (__eo_is_z (__eo_to_z (__run_evaluate yb))) (__eo_ite (__eo_is_neg (__eo_to_z (__run_evaluate yb))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_to_z (__run_evaluate yb)))) (__eo_mk_apply Term.int_pow2 (__eo_to_z (__run_evaluate yb)))))))
  | (Term.Apply (Term.Apply Term.bvlshr xb) yb) => (__eo_ite (__eo_gt (__eo_to_z (__run_evaluate yb)) (__bv_bitwidth (__eo_typeof xb))) (__eo_to_bin (__bv_bitwidth (__eo_typeof xb)) (Term.Numeral 0)) (__eo_to_bin (__bv_bitwidth (__eo_typeof xb)) (__eo_zdiv (__eo_to_z (__run_evaluate xb)) (__eo_ite (__eo_is_z (__eo_to_z (__run_evaluate yb))) (__eo_ite (__eo_is_neg (__eo_to_z (__run_evaluate yb))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__eo_to_z (__run_evaluate yb)))) (__eo_mk_apply Term.int_pow2 (__eo_to_z (__run_evaluate yb)))))))
  | (Term.Apply (Term.Apply Term.bvashr xb) yb) => (__eo_ite (__eo_eq (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 0)) (__run_evaluate (__eo_mk_apply (__eo_mk_apply Term.bvlshr (__run_evaluate xb)) (__run_evaluate yb))) (__run_evaluate (__eo_mk_apply Term.bvnot (__eo_mk_apply (__eo_mk_apply Term.bvlshr (__eo_mk_apply Term.bvnot (__run_evaluate xb))) (__run_evaluate yb)))))
  | (Term.Apply (Term.Apply Term.repeat n) xb) => (__run_evaluate (__eo_ite (__eo_and (__eo_is_z (__run_evaluate n)) (__eo_not (__eo_is_neg (__run_evaluate n)))) (__bv_unfold_repeat_rec (__run_evaluate n) (__run_evaluate xb)) (__eo_mk_apply (__eo_mk_apply Term.repeat (__run_evaluate n)) (__run_evaluate xb))))
  | (Term.Apply (Term.Apply Term.sign_extend n) xb) => (__eo_concat (__run_evaluate (__eo_ite (__eo_and (__eo_is_z (__run_evaluate n)) (__eo_not (__eo_is_neg (__run_evaluate n)))) (__bv_unfold_repeat_rec (__run_evaluate n) (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))))) (__eo_mk_apply (__eo_mk_apply Term.repeat (__run_evaluate n)) (__eo_extract (__run_evaluate xb) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral (-1 : eo_lit_Int))))))) (__run_evaluate xb))
  | (Term.Apply (Term.Apply Term.zero_extend n) xb) => (__eo_concat (__run_evaluate (__eo_ite (__eo_and (__eo_is_z (__run_evaluate n)) (__eo_not (__eo_is_neg (__run_evaluate n)))) (__bv_unfold_repeat_rec (__run_evaluate n) (Term.Binary 1 0)) (__eo_mk_apply (__eo_mk_apply Term.repeat (__run_evaluate n)) (Term.Binary 1 0)))) (__run_evaluate xb))
  | (Term.Apply (Term.Apply Term._at_bv n) m) => (__eo_to_bin (__run_evaluate m) (__run_evaluate n))
  | (Term.Apply Term._at_bvsize xb) => (__bv_bitwidth (__eo_typeof xb))
  | (Term.Apply (Term.Apply Term.int_to_bv n) m) => (__eo_to_bin (__run_evaluate n) (__run_evaluate m))
  | (Term.Apply Term.ubv_to_int xb) => (__eo_to_z (__run_evaluate xb))
  | (Term.Apply Term.sbv_to_int xb) => (__eo_ite (__eo_eq (__bv_bitwidth (__eo_typeof (__run_evaluate xb))) (Term.Numeral 0)) (Term.Numeral 0) (__eo_ite (__eo_eq (__eo_extract xb (__eo_add (__bv_bitwidth (__eo_typeof xb)) (Term.Numeral (-1 : eo_lit_Int))) (__eo_add (__bv_bitwidth (__eo_typeof xb)) (Term.Numeral (-1 : eo_lit_Int)))) (Term.Binary 1 0)) (__eo_to_z (__run_evaluate xb)) (__eo_add (__eo_to_z (__run_evaluate xb)) (__eo_neg (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof (__run_evaluate xb)))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof (__run_evaluate xb)))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__bv_bitwidth (__eo_typeof (__run_evaluate xb))))) (__eo_mk_apply Term.int_pow2 (__bv_bitwidth (__eo_typeof (__run_evaluate xb)))))))))
  | z => z


partial def __evaluate_list : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.__eo_List_cons t) ts) => (__eo_cons Term.__eo_List_cons (__run_evaluate t) (__evaluate_list ts))
  | Term.__eo_List_nil => Term.__eo_List_nil
  | _ => Term.Stuck


partial def __eo_prog_evaluate : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (__eo_mk_apply (Term.Apply Term.eq t) (__run_evaluate t))


partial def __eo_prog_distinct_values : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (__eo_requires (__eo_ite (__eo_eq t s) (Term.Boolean false) (__are_distinct_terms_list (Term.Apply (Term.Apply Term.__eo_List_cons t) (Term.Apply (Term.Apply Term.__eo_List_cons s) Term.__eo_List_nil)) (__eo_typeof t))) (Term.Boolean true) (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t) s)))


partial def __get_aci_normal_form : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.or b1) b2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.or) (__get_ai_norm (Term.Apply (Term.Apply Term.or b1) b2)))
  | (Term.Apply (Term.Apply Term.and b1) b2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.and) (__get_ai_norm (Term.Apply (Term.Apply Term.and b1) b2)))
  | (Term.Apply (Term.Apply Term.re_union r1) r2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.re_union) (__get_ai_norm (Term.Apply (Term.Apply Term.re_union r1) r2)))
  | (Term.Apply (Term.Apply Term.re_inter r1) r2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.re_inter) (__get_ai_norm (Term.Apply (Term.Apply Term.re_inter r1) r2)))
  | (Term.Apply (Term.Apply Term.bvor xb1) xb2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.bvor) (__get_ai_norm (Term.Apply (Term.Apply Term.bvor xb1) xb2)))
  | (Term.Apply (Term.Apply Term.bvand xb1) xb2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.bvand) (__get_ai_norm (Term.Apply (Term.Apply Term.bvand xb1) xb2)))
  | (Term.Apply (Term.Apply Term.bvxor xb1) xb2) => (__eo_mk_apply (Term.Apply Term._at__at_aci_sorted Term.bvxor) (__get_a_norm (Term.Apply (Term.Apply Term.bvxor xb1) xb2)))
  | (Term.Apply (Term.Apply Term.str_concat xs1) xs2) => (__get_a_norm (Term.Apply (Term.Apply Term.str_concat xs1) xs2))
  | (Term.Apply (Term.Apply Term.re_concat r1) r2) => (__get_a_norm (Term.Apply (Term.Apply Term.re_concat r1) r2))
  | (Term.Apply (Term.Apply Term.concat xb1) xb2) => (__get_a_norm (Term.Apply (Term.Apply Term.concat xb1) xb2))
  | x => x


partial def __eo_prog_aci_norm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq a) b) => (__eo_requires (__eo_ite (__aci_norm_eq (__get_aci_normal_form a) b) (Term.Boolean true) (__eo_ite (__aci_norm_eq (__get_aci_normal_form b) a) (Term.Boolean true) (__aci_norm_eq (__get_aci_normal_form a) (__get_aci_normal_form b)))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq a) b))
  | _ => Term.Stuck


partial def __eo_l_2___is_absorb_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, b, zero => (Term.Boolean false)


partial def __eo_l_1___is_absorb_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, (Term.Apply (Term.Apply __eo_lv_f_2 a) b), zero => (__eo_ite (__eo_eq f __eo_lv_f_2) (__eo_ite (__is_absorb_rec f a zero) (Term.Boolean true) (__is_absorb_rec f b zero)) (__eo_l_2___is_absorb_rec f (Term.Apply (Term.Apply __eo_lv_f_2 a) b) zero))
  | __eo_dv_1, __eo_dv_2, __eo_dv_3 => (__eo_l_2___is_absorb_rec __eo_dv_1 __eo_dv_2 __eo_dv_3)


partial def __is_absorb_rec : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | f, zero, __eo_lv_zero_2 => (__eo_ite (__eo_eq zero __eo_lv_zero_2) (Term.Boolean true) (__eo_l_1___is_absorb_rec f zero __eo_lv_zero_2))


partial def __get_zero : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.or b1) b2) => (Term.Boolean true)
  | (Term.Apply (Term.Apply Term.and b1) b2) => (Term.Boolean false)
  | (Term.Apply (Term.Apply Term.re_union r1) r2) => Term.re_all
  | (Term.Apply (Term.Apply Term.re_inter r1) r2) => Term.re_none
  | (Term.Apply (Term.Apply Term.re_concat r1) r2) => Term.re_none
  | (Term.Apply (Term.Apply Term.bvor xb1) xb2) => (__eo_to_bin (__bv_bitwidth (__eo_typeof xb1)) (__eo_add (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof xb1))) (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof xb1))) (Term.Numeral 0) (__arith_eval_int_pow_2_rec (__bv_bitwidth (__eo_typeof xb1)))) (__eo_mk_apply Term.int_pow2 (__bv_bitwidth (__eo_typeof xb1)))) (Term.Numeral (-1 : eo_lit_Int))))
  | (Term.Apply (Term.Apply Term.bvand xb1) xb2) => (__eo_to_bin (__bv_bitwidth (__eo_typeof xb1)) (Term.Numeral 0))
  | _ => Term.Stuck


partial def __is_absorb : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply f t1) t2), zero => (__is_absorb_rec f (Term.Apply (Term.Apply f t1) t2) zero)
  | _, _ => Term.Stuck


partial def __eo_prog_absorb : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t) zero) => (__eo_requires (__get_zero t) zero (__eo_requires (__is_absorb t zero) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq t) zero)))
  | _ => Term.Stuck


partial def __compute_card : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term.Bool => (Term.Numeral 2)
  | (Term.Apply Term.BitVec n) => (__eo_ite (__eo_is_z n) (__eo_ite (__eo_is_neg n) (Term.Numeral 0) (__arith_eval_int_pow_2_rec n)) (Term.Apply Term.int_pow2 n))
  | _ => Term.Stuck


partial def __eo_prog_distinct_card_conflict : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean false)) => (__eo_requires (__eo_gt (__eo_list_len Term.__eo_List_cons xs) (__compute_card (__assoc_nil_nth_type Term.__eo_List_cons xs (Term.Numeral 0)))) (Term.Boolean true) (Term.Apply (Term.Apply Term.eq (Term.Apply Term.distinct xs)) (Term.Boolean false)))
  | _ => Term.Stuck


partial def __eo_prog_trust : Term -> Proof -> Term
  | Term.Stuck , _  => Term.Stuck
  | F, (Proof.pf P) => F
  | _, _ => Term.Stuck


partial def __eo_typeof_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.FunType T) U), V => (__eo_requires T V U)
  | _, _ => Term.Stuck


partial def __eo_typeof__at__at_pair : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | U, T => (Term.Apply (Term.Apply Term._at__at_Pair U) T)


partial def __eo_typeof_ite : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Bool, A => (Term.Apply (Term.Apply Term.FunType A) A)
  | _, _ => Term.Stuck


partial def __eo_typeof_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | A => (Term.Apply (Term.Apply Term.FunType A) Term.Bool)


partial def __eo_typeof_lambda : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List, L, B => (__get_lambda_type L B)
  | _, _, _ => Term.Stuck


partial def __eo_typeof_distinct : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List, xs => (__eo_requires (__assoc_nil_same_type Term.__eo_List_cons xs) (Term.Boolean true) Term.Bool)
  | _, _ => Term.Stuck


partial def __eo_typeof__at_purify : Term -> Term
  | Term.Stuck  => Term.Stuck
  | A => A


partial def __eo_typeof_plus : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__arith_typeunion T U)


partial def __eo_typeof__ : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__arith_typeunion T U)


partial def __eo_typeof_mult : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__arith_typeunion T U)


partial def __eo_typeof_lt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Bool))


partial def __eo_typeof_leq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Bool))


partial def __eo_typeof_gt : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Bool))


partial def __eo_typeof_geq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Bool))


partial def __eo_typeof_to_real : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (__eo_requires (__is_arith_type T) (Term.Boolean true) Term.Real)


partial def __eo_typeof_to_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (__eo_requires (__is_arith_type T) (Term.Boolean true) Term.Int)


partial def __eo_typeof_is_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (__eo_requires (__is_arith_type T) (Term.Boolean true) Term.Bool)


partial def __eo_typeof_abs : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (__eo_requires (__is_arith_type T) (Term.Boolean true) T)


partial def __eo_typeof___eoo___2 : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (__eo_requires (__is_arith_type T) (Term.Boolean true) T)


partial def __eo_typeof_select : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Array U) T) => (Term.Apply (Term.Apply Term.FunType U) T)
  | _ => Term.Stuck


partial def __eo_typeof_store : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Array U) T) => (Term.Apply (Term.Apply Term.FunType U) (Term.Apply (Term.Apply Term.FunType T) (Term.Apply (Term.Apply Term.Array U) T)))
  | _ => Term.Stuck


partial def __eo_typeof__at_array_deq_diff : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.Array T) U), (Term.Apply (Term.Apply Term.Array __eo_lv_T_2) __eo_lv_U_2) => (__eo_requires (__eo_and (__eo_eq T __eo_lv_T_2) (__eo_eq U __eo_lv_U_2)) (Term.Boolean true) T)
  | _, _ => Term.Stuck


partial def __eo_typeof__at_bvsize : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => Term.Int
  | _ => Term.Stuck


partial def __eo_typeof_concat : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec n), (Term.Apply Term.BitVec m) => (__eo_mk_apply Term.BitVec (__eo_add n m))
  | _, _ => Term.Stuck


partial def __eo_typeof_extract : Term -> Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, h, Term.Int, l, (Term.Apply Term.BitVec n) => (__eo_mk_apply Term.BitVec (__eo_requires (__eo_gt (__eo_add l (Term.Numeral 1)) (Term.Numeral 0)) (Term.Boolean true) (__eo_requires (__eo_gt n h) (Term.Boolean true) (__eo_add (__eo_add h (__eo_neg l)) (Term.Numeral 1)))))
  | _, _, _, _, _ => Term.Stuck


partial def __eo_typeof_repeat : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, i, (Term.Apply Term.BitVec n) => (__eo_mk_apply Term.BitVec (__eo_mul i n))
  | _, _, _ => Term.Stuck


partial def __eo_typeof_bvnot : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec m)
  | _ => Term.Stuck


partial def __eo_typeof_bvand : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvnand : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvnor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvxor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvxnor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvcomp : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec (Term.Numeral 1)))
  | _ => Term.Stuck


partial def __eo_typeof_bvneg : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec m)
  | _ => Term.Stuck


partial def __eo_typeof_bvadd : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvmul : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvudiv : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvurem : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvsub : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvsdiv : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvsrem : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvsmod : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvult : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvule : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvugt : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvuge : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvslt : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvsle : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvsgt : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvsge : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvshl : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvlshr : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_bvashr : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec m))
  | _ => Term.Stuck


partial def __eo_typeof_zero_extend : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, i, (Term.Apply Term.BitVec m) => (__eo_mk_apply Term.BitVec (__eo_add m i))
  | _, _, _ => Term.Stuck


partial def __eo_typeof_sign_extend : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, i, (Term.Apply Term.BitVec m) => (__eo_mk_apply Term.BitVec (__eo_add m i))
  | _, _, _ => Term.Stuck


partial def __eo_typeof_rotate_left : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Int, (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec m)
  | _, _ => Term.Stuck


partial def __eo_typeof_rotate_right : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Int, (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec m)
  | _, _ => Term.Stuck


partial def __eo_typeof_bvite : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec (Term.Numeral 1)), T => (Term.Apply (Term.Apply Term.FunType T) T)
  | _, _ => Term.Stuck


partial def __eo_typeof_bvuaddo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvnego : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => Term.Bool
  | _ => Term.Stuck


partial def __eo_typeof_bvsaddo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvumulo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvsmulo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvusubo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvssubo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvsdivo : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_bvultbv : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec (Term.Numeral 1)))
  | _ => Term.Stuck


partial def __eo_typeof_bvsltbv : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.BitVec m)) (Term.Apply Term.BitVec (Term.Numeral 1)))
  | _ => Term.Stuck


partial def __eo_typeof_bvredand : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec (Term.Numeral 1))
  | _ => Term.Stuck


partial def __eo_typeof_bvredor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (Term.Apply Term.BitVec (Term.Numeral 1))
  | _ => Term.Stuck


partial def __eo_typeof__at_bit : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Int, (Term.Apply Term.BitVec m) => Term.Bool
  | _, _ => Term.Stuck


partial def __eo_typeof__at_from_bools : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Bool, (Term.Apply Term.BitVec n) => (__eo_mk_apply Term.BitVec (__eo_add (Term.Numeral 1) n))
  | _, _ => Term.Stuck


partial def __eo_typeof__at_bv : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, Term.Int, w => (Term.Apply Term.BitVec w)
  | _, _, _ => Term.Stuck


partial def __eo_typeof_seq_empty : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Type, __eo_disamb_type_seq_empty_var => (__eo_disamb_type_seq_empty __eo_disamb_type_seq_empty_var)
  | _, _ => Term.Stuck


partial def __eo_typeof_str_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => Term.Int
  | _ => Term.Stuck


partial def __eo_typeof_str_concat : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply Term.Seq T))
  | _ => Term.Stuck


partial def __eo_typeof_str_substr : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq T)))
  | _ => Term.Stuck


partial def __eo_typeof_str_contains : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_str_replace : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply Term.Seq T)))
  | _ => Term.Stuck


partial def __eo_typeof_str_indexof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | _ => Term.Stuck


partial def __eo_typeof_str_at : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq T))
  | _ => Term.Stuck


partial def __eo_typeof_str_prefixof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_str_suffixof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_str_rev : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply Term.Seq T)
  | _ => Term.Stuck


partial def __eo_typeof_str_update : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply Term.Seq T)))
  | _ => Term.Stuck


partial def __eo_typeof_str_replace_all : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply Term.Seq T)))
  | _ => Term.Stuck


partial def __eo_typeof_seq_unit : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (Term.Apply Term.Seq T)


partial def __eo_typeof_seq_nth : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType Term.Int) T)
  | _ => Term.Stuck


partial def __eo_typeof__at_strings_deq_diff : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T), (Term.Apply Term.Seq __eo_lv_T_2) => (__eo_requires (__eo_eq T __eo_lv_T_2) (Term.Boolean true) Term.Int)
  | _, _ => Term.Stuck


partial def __eo_typeof__at_strings_num_occur : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) Term.Int)
  | _ => Term.Stuck


partial def __eo_typeof__at_strings_occur_index : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq T)) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | _ => Term.Stuck


partial def __eo_typeof__at_strings_replace_all_result : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq T))
  | _ => Term.Stuck


partial def __eo_typeof__at_witness_string_length : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Type, T => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) T))
  | _, _ => Term.Stuck


partial def __eo_typeof_is : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | C, D => Term.Bool


partial def __eo_typeof_update : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | S, D, T => D


partial def __eo_typeof_tuple : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_cons Term.Tuple T U)


partial def __eo_typeof_tuple_select : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, i, T => (__eo_list_nth Term.Tuple T i)
  | _, _, _ => Term.Stuck


partial def __eo_typeof_tuple_update : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, i, T, U => (__eo_requires U (__eo_list_nth Term.Tuple T i) T)
  | _, _, _, _ => Term.Stuck


partial def __eo_typeof_set_empty : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Type, __eo_disamb_type_set_empty_var => (__eo_disamb_type_set_empty __eo_disamb_type_set_empty_var)
  | _, _ => Term.Stuck


partial def __eo_typeof_set_singleton : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (Term.Apply Term.Set T)


partial def __eo_typeof_set_union : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Set T)) (Term.Apply Term.Set T))
  | _ => Term.Stuck


partial def __eo_typeof_set_inter : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Set T)) (Term.Apply Term.Set T))
  | _ => Term.Stuck


partial def __eo_typeof_set_minus : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Set T)) (Term.Apply Term.Set T))
  | _ => Term.Stuck


partial def __eo_typeof_set_member : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Set T)) Term.Bool)


partial def __eo_typeof_set_subset : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Set T)) Term.Bool)
  | _ => Term.Stuck


partial def __eo_typeof_set_choose : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => T
  | _ => Term.Stuck


partial def __eo_typeof_set_is_empty : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => Term.Bool
  | _ => Term.Stuck


partial def __eo_typeof_set_is_singleton : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T) => Term.Bool
  | _ => Term.Stuck


partial def __eo_typeof_set_insert : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.__eo_List, (Term.Apply Term.Set T) => (Term.Apply Term.Set T)
  | _, _ => Term.Stuck


partial def __eo_typeof__at_sets_deq_diff : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Set T), (Term.Apply Term.Set __eo_lv_T_2) => (__eo_requires (__eo_eq T __eo_lv_T_2) (Term.Boolean true) T)
  | _, _ => Term.Stuck


partial def __eo_typeof_qdiv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Real))


partial def __eo_typeof_qdiv_total : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | T, U => (__eo_requires (__is_arith_type T) (Term.Boolean true) (__eo_requires (__is_arith_type U) (Term.Boolean true) Term.Real))


partial def __eo_typeof__at__at_mon : Term -> Term
  | Term.Stuck  => Term.Stuck
  | T => (Term.Apply (Term.Apply Term.FunType Term.Real) Term._at__at_Monomial)


partial def __eo_typeof__at_quantifiers_skolemize : Term -> Term -> Term -> Term -> Term
  | Term.Stuck , _ , _ , _  => Term.Stuck
  | _ , Term.Stuck , _ , _  => Term.Stuck
  | _ , _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , _ , Term.Stuck  => Term.Stuck
  | Term.Bool, F, Term.Int, i => (__assoc_nil_nth_type Term.__eo_List_cons (__get_var_list F) i)
  | _, _, _, _ => Term.Stuck


partial def __eo_typeof_int_to_bv : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Int, w => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.BitVec w))
  | _, _ => Term.Stuck


partial def __eo_typeof_ubv_to_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => Term.Int
  | _ => Term.Stuck


partial def __eo_typeof_sbv_to_int : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => Term.Int
  | _ => Term.Stuck


partial def __eo_typeof__at__at_aci_sorted : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | U, T => T


partial def __eo_typeof__at_const : Term -> Term -> Term -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | _ , Term.Stuck , _  => Term.Stuck
  | _ , _ , Term.Stuck  => Term.Stuck
  | Term.Int, Term.Type, T => T
  | _, _, _ => Term.Stuck


partial def __eo_typeof_fun_type : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Type, Term.Type => Term.Type
  | _, _ => Term.Stuck


partial def __eo_typeof_main : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term.Type => Term.Type
  | (Term.Apply (Term.Apply Term.FunType __eo_T) __eo_U) => (__eo_typeof_fun_type (__eo_typeof __eo_T) (__eo_typeof __eo_U))
  | Term.Bool => Term.Type
  | (Term.Boolean true) => Term.Bool
  | (Term.Boolean false) => Term.Bool
  | Term.__eo_List => Term.Type
  | Term.__eo_List_nil => Term.__eo_List
  | (Term.Apply Term.__eo_List_cons __eo_x1) => (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
  | Term.Int => Term.Type
  | Term.Real => Term.Type
  | Term.BitVec => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Type)
  | Term.Char => Term.Type
  | Term.Seq => (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type)
  | Term._at__at_Pair => (Term.Apply (Term.Apply Term.FunType Term.Type) (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type))
  | (Term.Apply (Term.Apply Term._at__at_pair __eo_x1) __eo_x2) => (__eo_typeof__at__at_pair (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | Term._at__at_result_null => Term.Bool
  | Term._at__at_result_invalid => Term.Bool
  | (Term.Apply (Term.Apply Term.ite __eo_x1) __eo_x2) => (__eo_typeof_ite (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | Term.not => (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool)
  | Term.or => (Term.Apply (Term.Apply Term.FunType Term.Bool) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | Term.and => (Term.Apply (Term.Apply Term.FunType Term.Bool) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | Term.imp => (Term.Apply (Term.Apply Term.FunType Term.Bool) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | Term.xor => (Term.Apply (Term.Apply Term.FunType Term.Bool) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | (Term.Apply Term.eq __eo_x1) => (__eo_typeof_eq (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.lambda __eo_x1) __eo_x2) => (__eo_typeof_lambda (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2))
  | (Term.Apply Term.distinct __eo_x1) => (__eo_typeof_distinct (__eo_typeof __eo_x1) __eo_x1)
  | (Term._at_purify __eo_x1) => (__eo_typeof__at_purify (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.plus __eo_x1) __eo_x2) => (__eo_typeof_plus (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.neg __eo_x1) __eo_x2) => (__eo_typeof__ (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.mult __eo_x1) __eo_x2) => (__eo_typeof_mult (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.lt __eo_x1) __eo_x2) => (__eo_typeof_lt (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.leq __eo_x1) __eo_x2) => (__eo_typeof_leq (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.gt __eo_x1) __eo_x2) => (__eo_typeof_gt (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.geq __eo_x1) __eo_x2) => (__eo_typeof_geq (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply Term.to_real __eo_x1) => (__eo_typeof_to_real (__eo_typeof __eo_x1))
  | (Term.Apply Term.to_int __eo_x1) => (__eo_typeof_to_int (__eo_typeof __eo_x1))
  | (Term.Apply Term.is_int __eo_x1) => (__eo_typeof_is_int (__eo_typeof __eo_x1))
  | (Term.Apply Term.abs __eo_x1) => (__eo_typeof_abs (__eo_typeof __eo_x1))
  | (Term.Apply Term.__eoo_neg_2 __eo_x1) => (__eo_typeof___eoo___2 (__eo_typeof __eo_x1))
  | Term.div => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | Term.mod => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | Term.divisible => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Bool))
  | Term.int_pow2 => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)
  | Term.int_log2 => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)
  | Term.int_ispow2 => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Bool)
  | Term.div_total => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | Term.mod_total => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | Term._at_int_div_by_zero => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)
  | Term._at_mod_by_zero => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)
  | Term.Array => (Term.Apply (Term.Apply Term.FunType Term.Type) (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type))
  | (Term.Apply Term.select __eo_x1) => (__eo_typeof_select (__eo_typeof __eo_x1))
  | (Term.Apply Term.store __eo_x1) => (__eo_typeof_store (__eo_typeof __eo_x1))
  | (Term._at_array_deq_diff __eo_x1 __eo_x2) => (__eo_typeof__at_array_deq_diff (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply Term._at_bvsize __eo_x1) => (__eo_typeof__at_bvsize (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.concat __eo_x1) __eo_x2) => (__eo_typeof_concat (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.extract __eo_x1) __eo_x2) __eo_x3) => (__eo_typeof_extract (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2) __eo_x2 (__eo_typeof __eo_x3))
  | (Term.Apply (Term.Apply Term.repeat __eo_x1) __eo_x2) => (__eo_typeof_repeat (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2))
  | (Term.Apply Term.bvnot __eo_x1) => (__eo_typeof_bvnot (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvand __eo_x1) => (__eo_typeof_bvand (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvor __eo_x1) => (__eo_typeof_bvor (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvnand __eo_x1) => (__eo_typeof_bvnand (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvnor __eo_x1) => (__eo_typeof_bvnor (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvxor __eo_x1) => (__eo_typeof_bvxor (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvxnor __eo_x1) => (__eo_typeof_bvxnor (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvcomp __eo_x1) => (__eo_typeof_bvcomp (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvneg __eo_x1) => (__eo_typeof_bvneg (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvadd __eo_x1) => (__eo_typeof_bvadd (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvmul __eo_x1) => (__eo_typeof_bvmul (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvudiv __eo_x1) => (__eo_typeof_bvudiv (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvurem __eo_x1) => (__eo_typeof_bvurem (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsub __eo_x1) => (__eo_typeof_bvsub (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsdiv __eo_x1) => (__eo_typeof_bvsdiv (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsrem __eo_x1) => (__eo_typeof_bvsrem (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsmod __eo_x1) => (__eo_typeof_bvsmod (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvult __eo_x1) => (__eo_typeof_bvult (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvule __eo_x1) => (__eo_typeof_bvule (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvugt __eo_x1) => (__eo_typeof_bvugt (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvuge __eo_x1) => (__eo_typeof_bvuge (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvslt __eo_x1) => (__eo_typeof_bvslt (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsle __eo_x1) => (__eo_typeof_bvsle (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsgt __eo_x1) => (__eo_typeof_bvsgt (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsge __eo_x1) => (__eo_typeof_bvsge (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvshl __eo_x1) => (__eo_typeof_bvshl (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvlshr __eo_x1) => (__eo_typeof_bvlshr (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvashr __eo_x1) => (__eo_typeof_bvashr (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.zero_extend __eo_x1) __eo_x2) => (__eo_typeof_zero_extend (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.sign_extend __eo_x1) __eo_x2) => (__eo_typeof_sign_extend (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.rotate_left __eo_x1) __eo_x2) => (__eo_typeof_rotate_left (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.rotate_right __eo_x1) __eo_x2) => (__eo_typeof_rotate_right (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.bvite __eo_x1) __eo_x2) => (__eo_typeof_bvite (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply Term.bvuaddo __eo_x1) => (__eo_typeof_bvuaddo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvnego __eo_x1) => (__eo_typeof_bvnego (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsaddo __eo_x1) => (__eo_typeof_bvsaddo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvumulo __eo_x1) => (__eo_typeof_bvumulo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsmulo __eo_x1) => (__eo_typeof_bvsmulo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvusubo __eo_x1) => (__eo_typeof_bvusubo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvssubo __eo_x1) => (__eo_typeof_bvssubo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsdivo __eo_x1) => (__eo_typeof_bvsdivo (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvultbv __eo_x1) => (__eo_typeof_bvultbv (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvsltbv __eo_x1) => (__eo_typeof_bvsltbv (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvredand __eo_x1) => (__eo_typeof_bvredand (__eo_typeof __eo_x1))
  | (Term.Apply Term.bvredor __eo_x1) => (__eo_typeof_bvredor (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term._at_bit __eo_x1) __eo_x2) => (__eo_typeof__at_bit (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term._at_from_bools __eo_x1) __eo_x2) => (__eo_typeof__at_from_bools (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term._at_bv __eo_x1) __eo_x2) => (__eo_typeof__at_bv (__eo_typeof __eo_x1) (__eo_typeof __eo_x2) __eo_x2)
  | Term.RegLan => Term.Type
  | (Term.seq_empty __eo_x1) => (__eo_typeof_seq_empty (__eo_typeof __eo_x1) __eo_x1)
  | (Term.Apply Term.str_len __eo_x1) => (__eo_typeof_str_len (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_concat __eo_x1) => (__eo_typeof_str_concat (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_substr __eo_x1) => (__eo_typeof_str_substr (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_contains __eo_x1) => (__eo_typeof_str_contains (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_replace __eo_x1) => (__eo_typeof_str_replace (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_indexof __eo_x1) => (__eo_typeof_str_indexof (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_at __eo_x1) => (__eo_typeof_str_at (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_prefixof __eo_x1) => (__eo_typeof_str_prefixof (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_suffixof __eo_x1) => (__eo_typeof_str_suffixof (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_rev __eo_x1) => (__eo_typeof_str_rev (__eo_typeof __eo_x1))
  | (Term.Apply Term.str_update __eo_x1) => (__eo_typeof_str_update (__eo_typeof __eo_x1))
  | Term.str_to_lower => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply Term.Seq Term.Char))
  | Term.str_to_upper => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply Term.Seq Term.Char))
  | Term.str_to_code => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Int)
  | Term.str_from_code => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq Term.Char))
  | Term.str_is_digit => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Bool)
  | Term.str_to_int => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Int)
  | Term.str_from_int => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq Term.Char))
  | Term.str_lt => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Bool))
  | Term.str_leq => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Bool))
  | (Term.Apply Term.str_replace_all __eo_x1) => (__eo_typeof_str_replace_all (__eo_typeof __eo_x1))
  | Term.str_replace_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply Term.Seq Term.Char))))
  | Term.str_replace_re_all => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply Term.Seq Term.Char))))
  | Term.str_indexof_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)))
  | Term.re_allchar => Term.RegLan
  | Term.re_none => Term.RegLan
  | Term.re_all => Term.RegLan
  | Term.str_to_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.RegLan)
  | Term.re_mult => (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan)
  | Term.re_plus => (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan)
  | Term.re_exp => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan))
  | Term.re_opt => (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan)
  | Term.re_comp => (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan)
  | Term.re_range => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.RegLan))
  | Term.re_concat => (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan))
  | Term.re_inter => (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan))
  | Term.re_union => (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan))
  | Term.re_diff => (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan))
  | Term.re_loop => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.RegLan)))
  | Term.str_in_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.Bool))
  | (Term.Apply Term.seq_unit __eo_x1) => (__eo_typeof_seq_unit (__eo_typeof __eo_x1))
  | (Term.Apply Term.seq_nth __eo_x1) => (__eo_typeof_seq_nth (__eo_typeof __eo_x1))
  | Term._at_re_unfold_pos_component => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply Term.Seq Term.Char))))
  | (Term.Apply (Term.Apply Term._at_strings_deq_diff __eo_x1) __eo_x2) => (__eo_typeof__at_strings_deq_diff (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | Term._at_strings_stoi_result => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | Term._at_strings_stoi_non_digit => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) Term.Int)
  | Term._at_strings_itos_result => (Term.Apply (Term.Apply Term.FunType Term.Int) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int))
  | (Term.Apply Term._at_strings_num_occur __eo_x1) => (__eo_typeof__at_strings_num_occur (__eo_typeof __eo_x1))
  | Term._at_strings_num_occur_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) Term.Int))
  | (Term.Apply Term._at_strings_occur_index __eo_x1) => (__eo_typeof__at_strings_occur_index (__eo_typeof __eo_x1))
  | Term._at_strings_occur_index_re => (Term.Apply (Term.Apply Term.FunType (Term.Apply Term.Seq Term.Char)) (Term.Apply (Term.Apply Term.FunType Term.RegLan) (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Int)))
  | (Term._at_strings_replace_all_result __eo_x1) => (__eo_typeof__at_strings_replace_all_result (__eo_typeof __eo_x1))
  | (Term.Apply Term._at_witness_string_length __eo_x1) => (__eo_typeof__at_witness_string_length (__eo_typeof __eo_x1) __eo_x1)
  | (Term.Apply (Term.Apply Term.is __eo_x1) __eo_x2) => (__eo_typeof_is (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.update __eo_x1) __eo_x2) __eo_x3) => (__eo_typeof_update (__eo_typeof __eo_x1) (__eo_typeof __eo_x2) (__eo_typeof __eo_x3))
  | Term.UnitTuple => Term.Type
  | Term.Tuple => (Term.Apply (Term.Apply Term.FunType Term.Type) (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type))
  | Term.tuple_unit => Term.UnitTuple
  | (Term.Apply (Term.Apply Term.tuple __eo_x1) __eo_x2) => (__eo_typeof_tuple (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.tuple_select __eo_x1) __eo_x2) => (__eo_typeof_tuple_select (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update __eo_x1) __eo_x2) __eo_x3) => (__eo_typeof_tuple_update (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2) (__eo_typeof __eo_x3))
  | Term.Set => (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type)
  | (Term.set_empty __eo_x1) => (__eo_typeof_set_empty (__eo_typeof __eo_x1) __eo_x1)
  | (Term.Apply Term.set_singleton __eo_x1) => (__eo_typeof_set_singleton (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_union __eo_x1) => (__eo_typeof_set_union (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_inter __eo_x1) => (__eo_typeof_set_inter (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_minus __eo_x1) => (__eo_typeof_set_minus (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_member __eo_x1) => (__eo_typeof_set_member (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_subset __eo_x1) => (__eo_typeof_set_subset (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_choose __eo_x1) => (__eo_typeof_set_choose (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_is_empty __eo_x1) => (__eo_typeof_set_is_empty (__eo_typeof __eo_x1))
  | (Term.Apply Term.set_is_singleton __eo_x1) => (__eo_typeof_set_is_singleton (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.set_insert __eo_x1) __eo_x2) => (__eo_typeof_set_insert (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term._at_sets_deq_diff __eo_x1 __eo_x2) => (__eo_typeof__at_sets_deq_diff (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.qdiv __eo_x1) __eo_x2) => (__eo_typeof_qdiv (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.qdiv_total __eo_x1) __eo_x2) => (__eo_typeof_qdiv_total (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | Term._at_div_by_zero => (Term.Apply (Term.Apply Term.FunType Term.Real) Term.Real)
  | Term._at__at_Monomial => Term.Type
  | (Term.Apply Term._at__at_mon __eo_x1) => (__eo_typeof__at__at_mon (__eo_typeof __eo_x1))
  | Term._at__at_Polynomial => Term.Type
  | Term._at__at_poly_zero => Term._at__at_Polynomial
  | Term._at__at_poly => (Term.Apply (Term.Apply Term.FunType Term._at__at_Monomial) (Term.Apply (Term.Apply Term.FunType Term._at__at_Polynomial) Term._at__at_Polynomial))
  | Term.forall => (Term.Apply (Term.Apply Term.FunType Term.__eo_List) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | Term.exists => (Term.Apply (Term.Apply Term.FunType Term.__eo_List) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | (Term._at_quantifiers_skolemize __eo_x1 __eo_x2) => (__eo_typeof__at_quantifiers_skolemize (__eo_typeof __eo_x1) __eo_x1 (__eo_typeof __eo_x2) __eo_x2)
  | (Term.Apply Term.int_to_bv __eo_x1) => (__eo_typeof_int_to_bv (__eo_typeof __eo_x1) __eo_x1)
  | (Term.Apply Term.ubv_to_int __eo_x1) => (__eo_typeof_ubv_to_int (__eo_typeof __eo_x1))
  | (Term.Apply Term.sbv_to_int __eo_x1) => (__eo_typeof_sbv_to_int (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term._at__at_aci_sorted __eo_x1) __eo_x2) => (__eo_typeof__at__at_aci_sorted (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term._at_const __eo_x1 __eo_x2) => (__eo_typeof__at_const (__eo_typeof __eo_x1) (__eo_typeof __eo_x2) __eo_x2)
  | (Term.Apply __eo_f __eo_x) => (__eo_typeof_apply (__eo_typeof __eo_f) (__eo_typeof __eo_x))
  | _ => Term.Stuck


partial def __eo_lit_type_Numeral : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => Term.Int


partial def __eo_lit_type_Rational : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => Term.Real


partial def __eo_lit_type_Binary : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (__eo_mk_apply Term.BitVec (__eo_len t))


partial def __eo_lit_type_String : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (Term.Apply Term.Seq Term.Char)


partial def __eo_dt_constructors_main : Term -> Term
  | Term.Stuck  => Term.Stuck
  | _ => Term.Stuck


partial def __eo_dt_selectors_main : Term -> Term
  | Term.Stuck  => Term.Stuck
  | _ => Term.Stuck


partial def __eo_nil_bvand : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (__eo_not (__eo_to_bin m (Term.Numeral 0)))
  | _ => Term.Stuck


partial def __eo_nil_bvor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (__eo_to_bin m (Term.Numeral 0))
  | _ => Term.Stuck


partial def __eo_nil_bvxor : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (__eo_to_bin m (Term.Numeral 0))
  | _ => Term.Stuck


partial def __eo_nil_bvadd : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (__eo_to_bin m (Term.Numeral 0))
  | _ => Term.Stuck


partial def __eo_nil_bvmul : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.BitVec m) => (__eo_to_bin m (Term.Numeral 1))
  | _ => Term.Stuck


partial def __eo_nil_str_concat : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply Term.Seq T) => (__seq_empty (Term.Apply Term.Seq T))
  | _ => Term.Stuck


partial def __eo_nil : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.or, T => (Term.Boolean false)
  | Term.and, T => (Term.Boolean true)
  | Term.plus, T => (Term.Numeral 0)
  | Term.mult, T => (Term.Numeral 1)
  | Term.concat, T => (Term.Binary 0 0)
  | Term.bvand, T => (__eo_nil_bvand T)
  | Term.bvor, T => (__eo_nil_bvor T)
  | Term.bvxor, T => (__eo_nil_bvxor T)
  | Term.bvadd, T => (__eo_nil_bvadd T)
  | Term.bvmul, T => (__eo_nil_bvmul T)
  | Term._at_from_bools, T => (Term.Binary 0 0)
  | Term.str_concat, T => (__eo_nil_str_concat T)
  | Term.re_concat, T => (Term.Apply Term.str_to_re (Term.String ""))
  | Term.re_inter, T => Term.re_all
  | Term.re_union, T => Term.re_none
  | Term.Tuple, T => Term.UnitTuple
  | Term.tuple, T => Term.tuple_unit
  | Term._at__at_poly, T => Term._at__at_Polynomial
  | Term.__eo_List_cons, Term.__eo_List => Term.__eo_List_nil
  | _, _ => Term.Stuck


partial def __eo_Result : Term := Term.Bool
partial def __eo_prog_re_all_elim : Term := (Term.Apply (Term.Apply Term.eq Term.re_all) (Term.Apply Term.re_mult Term.re_allchar))
partial def __eo_prog_re_star_none : Term := (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult Term.re_none)) (Term.Apply Term.str_to_re (Term.String "")))
partial def __eo_prog_re_star_emp : Term := (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply Term.str_to_re (Term.String "")))


end

/- Definition of the checker -/

/- FIXME: make Int -/
abbrev CIndex := Term

/-
-/
inductive CIndexList : Type where
  | nil : CIndexList
  | cons : CIndex -> CIndexList -> CIndexList
deriving Repr, Inhabited

/-
-/
inductive CStateObj : Type where
  | assume : Term -> CStateObj
  | assume_push : Term -> CStateObj
  | proven : Term -> CStateObj
deriving Repr, Inhabited

/-
-/
inductive CState : Type where
  | nil : CState
  | cons : CStateObj -> CState -> CState
  | Stuck : CState
deriving Repr, Inhabited

/-
-/
inductive CCmd : Type where
  | assume_push : Term -> CCmd
  | check_proven : Term -> CCmd
  | scope : CIndex -> CCmd
  | process_scope : Term -> CIndex -> CCmd
  | ite_eq : Term -> CCmd
  | split : Term -> CCmd
  | resolution : Term -> Term -> CIndex -> CIndex -> CCmd
  | chain_resolution : Term -> Term -> CIndexList -> CCmd
  | chain_m_resolution : Term -> Term -> Term -> CIndexList -> CCmd
  | factoring : CIndex -> CCmd
  | reordering : Term -> CIndex -> CCmd
  | eq_resolve : CIndex -> CIndex -> CCmd
  | modus_ponens : CIndex -> CIndex -> CCmd
  | not_not_elim : CIndex -> CCmd
  | contra : CIndex -> CIndex -> CCmd
  | and_elim : Term -> CIndex -> CCmd
  | and_intro : CIndexList -> CCmd
  | not_or_elim : Term -> CIndex -> CCmd
  | implies_elim : CIndex -> CCmd
  | not_implies_elim1 : CIndex -> CCmd
  | not_implies_elim2 : CIndex -> CCmd
  | equiv_elim1 : CIndex -> CCmd
  | equiv_elim2 : CIndex -> CCmd
  | not_equiv_elim1 : CIndex -> CCmd
  | not_equiv_elim2 : CIndex -> CCmd
  | xor_elim1 : CIndex -> CCmd
  | xor_elim2 : CIndex -> CCmd
  | not_xor_elim1 : CIndex -> CCmd
  | not_xor_elim2 : CIndex -> CCmd
  | ite_elim1 : CIndex -> CCmd
  | ite_elim2 : CIndex -> CCmd
  | not_ite_elim1 : CIndex -> CCmd
  | not_ite_elim2 : CIndex -> CCmd
  | not_and : CIndex -> CCmd
  | cnf_and_pos : Term -> Term -> CCmd
  | cnf_and_neg : Term -> CCmd
  | cnf_or_pos : Term -> CCmd
  | cnf_or_neg : Term -> Term -> CCmd
  | cnf_implies_pos : Term -> CCmd
  | cnf_implies_neg1 : Term -> CCmd
  | cnf_implies_neg2 : Term -> CCmd
  | cnf_equiv_pos1 : Term -> CCmd
  | cnf_equiv_pos2 : Term -> CCmd
  | cnf_equiv_neg1 : Term -> CCmd
  | cnf_equiv_neg2 : Term -> CCmd
  | cnf_xor_pos1 : Term -> CCmd
  | cnf_xor_pos2 : Term -> CCmd
  | cnf_xor_neg1 : Term -> CCmd
  | cnf_xor_neg2 : Term -> CCmd
  | cnf_ite_pos1 : Term -> CCmd
  | cnf_ite_pos2 : Term -> CCmd
  | cnf_ite_pos3 : Term -> CCmd
  | cnf_ite_neg1 : Term -> CCmd
  | cnf_ite_neg2 : Term -> CCmd
  | cnf_ite_neg3 : Term -> CCmd
  | arrays_read_over_write : Term -> CIndex -> CCmd
  | arrays_read_over_write_contra : CIndex -> CCmd
  | arrays_read_over_write_1 : Term -> CCmd
  | arrays_ext : CIndex -> CCmd
  | refl : Term -> CCmd
  | symm : CIndex -> CCmd
  | trans : CIndexList -> CCmd
  | cong : Term -> CIndexList -> CCmd
  | nary_cong : Term -> CIndexList -> CCmd
  | pairwise_cong : Term -> CIndexList -> CCmd
  | true_intro : CIndex -> CCmd
  | true_elim : CIndex -> CCmd
  | false_intro : CIndex -> CCmd
  | false_elim : CIndex -> CCmd
  | ho_cong : CIndexList -> CCmd
  | distinct_elim : Term -> CCmd
  | distinct_true : Term -> CCmd
  | distinct_false : Term -> CCmd
  | lambda_elim : Term -> CCmd
  | arith_sum_ub : CIndexList -> CCmd
  | arith_mult_pos : Term -> Term -> CCmd
  | arith_mult_neg : Term -> Term -> CCmd
  | arith_trichotomy : CIndex -> CIndex -> CCmd
  | int_tight_ub : CIndex -> CCmd
  | int_tight_lb : CIndex -> CCmd
  | arith_mult_tangent : Term -> Term -> Term -> Term -> Term -> CCmd
  | arith_mult_sign : Term -> Term -> CCmd
  | arith_mult_abs_comparison : CIndexList -> CCmd
  | arith_reduction : Term -> CCmd
  | arith_poly_norm : Term -> CCmd
  | arith_poly_norm_rel : Term -> CIndex -> CCmd
  | bv_repeat_elim : Term -> CCmd
  | bv_smulo_elim : Term -> CCmd
  | bv_umulo_elim : Term -> CCmd
  | bv_bitwise_slicing : Term -> CCmd
  | bv_bitblast_step : Term -> CCmd
  | bv_poly_norm : Term -> CCmd
  | bv_poly_norm_eq : Term -> CIndex -> CCmd
  | string_length_pos : Term -> CCmd
  | string_length_non_empty : CIndex -> CCmd
  | concat_eq : Term -> CIndex -> CCmd
  | concat_unify : Term -> CIndex -> CIndex -> CCmd
  | concat_csplit : Term -> CIndex -> CIndex -> CCmd
  | concat_split : Term -> CIndex -> CIndex -> CCmd
  | concat_lprop : Term -> CIndex -> CIndex -> CCmd
  | concat_cprop : Term -> CIndex -> CIndex -> CCmd
  | string_decompose : Term -> CIndex -> CIndex -> CCmd
  | exists_string_length : Term -> Term -> Term -> CCmd
  | string_code_inj : Term -> Term -> CCmd
  | string_seq_unit_inj : CIndex -> CCmd
  | re_inter : CIndex -> CIndex -> CCmd
  | re_concat : CIndexList -> CCmd
  | re_unfold_pos : CIndex -> CCmd
  | re_unfold_neg_concat_fixed : Term -> CIndex -> CCmd
  | re_unfold_neg : CIndex -> CCmd
  | string_ext : CIndex -> CCmd
  | string_reduction : Term -> CCmd
  | string_eager_reduction : Term -> CCmd
  | arith_string_pred_entail : Term -> CCmd
  | arith_string_pred_safe_approx : Term -> CCmd
  | str_in_re_eval : Term -> CCmd
  | str_in_re_consume : Term -> CCmd
  | re_loop_elim : Term -> CCmd
  | re_eq_elim : Term -> CCmd
  | re_inter_inclusion : Term -> CCmd
  | re_union_inclusion : Term -> CCmd
  | str_in_re_concat_star_char : Term -> CCmd
  | str_in_re_sigma : Term -> CCmd
  | str_in_re_sigma_star : Term -> CCmd
  | str_ctn_multiset_subset : Term -> CCmd
  | str_overlap_split_ctn : Term -> CCmd
  | str_overlap_endpoints_ctn : Term -> CCmd
  | str_overlap_endpoints_indexof : Term -> CCmd
  | str_overlap_endpoints_replace : Term -> CCmd
  | str_indexof_re_eval : Term -> CCmd
  | str_replace_re_eval : Term -> CCmd
  | str_replace_re_all_eval : Term -> CCmd
  | seq_eval_op : Term -> CCmd
  | sets_singleton_inj : CIndex -> CCmd
  | sets_ext : CIndex -> CCmd
  | sets_eval_op : Term -> CCmd
  | sets_insert_elim : Term -> CCmd
  | ubv_to_int_elim : Term -> CCmd
  | int_to_bv_elim : Term -> CCmd
  | instantiate : Term -> CIndex -> CCmd
  | skolemize : CIndex -> CCmd
  | skolem_intro : Term -> CCmd
  | alpha_equiv : Term -> Term -> Term -> CCmd
  | beta_reduce : Term -> CCmd
  | quant_var_reordering : Term -> CCmd
  | exists_elim : Term -> CCmd
  | quant_unused_vars : Term -> CCmd
  | quant_merge_prenex : Term -> CCmd
  | quant_miniscope_and : Term -> CCmd
  | quant_miniscope_or : Term -> CCmd
  | quant_miniscope_ite : Term -> CCmd
  | quant_var_elim_eq : Term -> CCmd
  | quant_dt_split : Term -> CCmd
  | dt_split : Term -> CCmd
  | dt_inst : Term -> CCmd
  | dt_collapse_selector : Term -> CCmd
  | dt_collapse_tester : Term -> CCmd
  | dt_collapse_tester_singleton : Term -> CCmd
  | dt_cons_eq : Term -> CCmd
  | dt_cons_eq_clash : Term -> CCmd
  | dt_cycle : Term -> CCmd
  | dt_collapse_updater : Term -> CCmd
  | dt_updater_elim : Term -> CCmd
  | arith_div_total_zero_real : Term -> CCmd
  | arith_div_total_zero_int : Term -> CCmd
  | arith_int_div_total : Term -> Term -> CIndex -> CCmd
  | arith_int_div_total_one : Term -> CCmd
  | arith_int_div_total_zero : Term -> CCmd
  | arith_int_div_total_neg : Term -> Term -> CIndex -> CCmd
  | arith_int_mod_total : Term -> Term -> CIndex -> CCmd
  | arith_int_mod_total_one : Term -> CCmd
  | arith_int_mod_total_zero : Term -> CCmd
  | arith_int_mod_total_neg : Term -> Term -> CIndex -> CCmd
  | arith_elim_gt : Term -> Term -> CCmd
  | arith_elim_lt : Term -> Term -> CCmd
  | arith_elim_int_gt : Term -> Term -> CCmd
  | arith_elim_int_lt : Term -> Term -> CCmd
  | arith_elim_leq : Term -> Term -> CCmd
  | arith_leq_norm : Term -> Term -> CCmd
  | arith_geq_tighten : Term -> Term -> CCmd
  | arith_geq_norm1_int : Term -> Term -> CCmd
  | arith_geq_norm1_real : Term -> Term -> CCmd
  | arith_eq_elim_real : Term -> Term -> CCmd
  | arith_eq_elim_int : Term -> Term -> CCmd
  | arith_to_int_elim : Term -> CCmd
  | arith_to_int_elim_to_real : Term -> CCmd
  | arith_div_elim_to_real1 : Term -> Term -> CCmd
  | arith_div_elim_to_real2 : Term -> Term -> CCmd
  | arith_mod_over_mod_1 : Term -> Term -> CIndex -> CCmd
  | arith_mod_over_mod : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | arith_mod_over_mod_mult : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | arith_int_eq_conflict : Term -> Term -> CIndex -> CCmd
  | arith_int_geq_tighten : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | arith_divisible_elim : Term -> Term -> CIndex -> CCmd
  | arith_abs_eq : Term -> Term -> CCmd
  | arith_abs_int_gt : Term -> Term -> CCmd
  | arith_abs_real_gt : Term -> Term -> CCmd
  | arith_geq_ite_lift : Term -> Term -> Term -> Term -> CCmd
  | arith_leq_ite_lift : Term -> Term -> Term -> Term -> CCmd
  | arith_min_lt1 : Term -> Term -> CCmd
  | arith_min_lt2 : Term -> Term -> CCmd
  | arith_max_geq1 : Term -> Term -> CCmd
  | arith_max_geq2 : Term -> Term -> CCmd
  | array_read_over_write : Term -> Term -> Term -> CCmd
  | array_read_over_write2 : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | array_store_overwrite : Term -> Term -> Term -> Term -> CCmd
  | array_store_self : Term -> Term -> CCmd
  | array_read_over_write_split : Term -> Term -> Term -> Term -> CCmd
  | array_store_swap : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bool_double_not_elim : Term -> CCmd
  | bool_not_true : Term -> CIndex -> CCmd
  | bool_not_false : Term -> CIndex -> CCmd
  | bool_eq_true : Term -> CCmd
  | bool_eq_false : Term -> CCmd
  | bool_eq_nrefl : Term -> CCmd
  | bool_impl_false1 : Term -> CCmd
  | bool_impl_false2 : Term -> CCmd
  | bool_impl_true1 : Term -> CCmd
  | bool_impl_true2 : Term -> CCmd
  | bool_impl_elim : Term -> Term -> CCmd
  | bool_dual_impl_eq : Term -> Term -> CCmd
  | bool_and_conf : Term -> Term -> Term -> Term -> CCmd
  | bool_and_conf2 : Term -> Term -> Term -> Term -> CCmd
  | bool_or_taut : Term -> Term -> Term -> Term -> CCmd
  | bool_or_taut2 : Term -> Term -> Term -> Term -> CCmd
  | bool_or_de_morgan : Term -> Term -> Term -> CCmd
  | bool_implies_de_morgan : Term -> Term -> CCmd
  | bool_and_de_morgan : Term -> Term -> Term -> CCmd
  | bool_or_and_distrib : Term -> Term -> Term -> Term -> Term -> CCmd
  | bool_implies_or_distrib : Term -> Term -> Term -> Term -> CCmd
  | bool_xor_refl : Term -> CCmd
  | bool_xor_nrefl : Term -> CCmd
  | bool_xor_false : Term -> CCmd
  | bool_xor_true : Term -> CCmd
  | bool_xor_comm : Term -> Term -> CCmd
  | bool_xor_elim : Term -> Term -> CCmd
  | bool_not_xor_elim : Term -> Term -> CCmd
  | bool_not_eq_elim1 : Term -> Term -> CCmd
  | bool_not_eq_elim2 : Term -> Term -> CCmd
  | ite_neg_branch : Term -> Term -> Term -> CIndex -> CCmd
  | ite_then_true : Term -> Term -> CCmd
  | ite_else_false : Term -> Term -> CCmd
  | ite_then_false : Term -> Term -> CCmd
  | ite_else_true : Term -> Term -> CCmd
  | ite_then_lookahead_self : Term -> Term -> CCmd
  | ite_else_lookahead_self : Term -> Term -> CCmd
  | ite_then_lookahead_not_self : Term -> Term -> CCmd
  | ite_else_lookahead_not_self : Term -> Term -> CCmd
  | ite_expand : Term -> Term -> Term -> CCmd
  | bool_not_ite_elim : Term -> Term -> Term -> CCmd
  | ite_true_cond : Term -> Term -> CCmd
  | ite_false_cond : Term -> Term -> CCmd
  | ite_not_cond : Term -> Term -> Term -> CCmd
  | ite_eq_branch : Term -> Term -> CCmd
  | ite_then_lookahead : Term -> Term -> Term -> Term -> CCmd
  | ite_else_lookahead : Term -> Term -> Term -> Term -> CCmd
  | ite_then_neg_lookahead : Term -> Term -> Term -> Term -> CCmd
  | ite_else_neg_lookahead : Term -> Term -> Term -> Term -> CCmd
  | bv_concat_extract_merge : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_extract_extract : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_extract_whole : Term -> Term -> CIndex -> CCmd
  | bv_extract_concat_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_extract_concat_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_extract_concat_3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_extract_concat_4 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_eq_extract_elim1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_eq_extract_elim2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_eq_extract_elim3 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_extract_not : Term -> Term -> Term -> CCmd
  | bv_extract_sign_extend_1 : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_extract_sign_extend_2 : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_extract_sign_extend_3 : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_not_xor : Term -> Term -> Term -> CCmd
  | bv_and_simplify_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_and_simplify_2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_or_simplify_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_or_simplify_2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_xor_simplify_1 : Term -> Term -> Term -> Term -> CCmd
  | bv_xor_simplify_2 : Term -> Term -> Term -> Term -> CCmd
  | bv_xor_simplify_3 : Term -> Term -> Term -> Term -> CCmd
  | bv_ult_add_one : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_mult_slt_mult_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_mult_slt_mult_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_commutative_xor : Term -> Term -> CCmd
  | bv_commutative_comp : Term -> Term -> CCmd
  | bv_zero_extend_eliminate_0 : Term -> CCmd
  | bv_sign_extend_eliminate_0 : Term -> CCmd
  | bv_not_neq : Term -> CIndex -> CCmd
  | bv_ult_ones : Term -> Term -> Term -> CIndex -> CCmd
  | bv_concat_merge_const : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_commutative_add : Term -> Term -> CCmd
  | bv_sub_eliminate : Term -> Term -> CCmd
  | bv_ite_width_one : Term -> CCmd
  | bv_ite_width_one_not : Term -> CCmd
  | bv_eq_xor_solve : Term -> Term -> Term -> CCmd
  | bv_eq_not_solve : Term -> Term -> CCmd
  | bv_ugt_eliminate : Term -> Term -> CCmd
  | bv_uge_eliminate : Term -> Term -> CCmd
  | bv_sgt_eliminate : Term -> Term -> CCmd
  | bv_sge_eliminate : Term -> Term -> CCmd
  | bv_sle_eliminate : Term -> Term -> CCmd
  | bv_redor_eliminate : Term -> Term -> CIndex -> CCmd
  | bv_redand_eliminate : Term -> Term -> CIndex -> CCmd
  | bv_ule_eliminate : Term -> Term -> CCmd
  | bv_comp_eliminate : Term -> Term -> CCmd
  | bv_rotate_left_eliminate_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_rotate_left_eliminate_2 : Term -> Term -> CIndex -> CCmd
  | bv_rotate_right_eliminate_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_rotate_right_eliminate_2 : Term -> Term -> CIndex -> CCmd
  | bv_nand_eliminate : Term -> Term -> CCmd
  | bv_nor_eliminate : Term -> Term -> CCmd
  | bv_xnor_eliminate : Term -> Term -> CCmd
  | bv_sdiv_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_zero_extend_eliminate : Term -> Term -> CCmd
  | bv_uaddo_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_saddo_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_sdivo_eliminate : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_smod_eliminate : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_srem_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_usubo_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_ssubo_eliminate : Term -> Term -> Term -> CIndex -> CCmd
  | bv_nego_eliminate : Term -> Term -> CIndex -> CCmd
  | bv_ite_equal_children : Term -> Term -> CCmd
  | bv_ite_const_children_1 : Term -> CCmd
  | bv_ite_const_children_2 : Term -> CCmd
  | bv_ite_equal_cond_1 : Term -> Term -> Term -> Term -> CCmd
  | bv_ite_equal_cond_2 : Term -> Term -> Term -> Term -> CCmd
  | bv_ite_equal_cond_3 : Term -> Term -> Term -> Term -> Term -> CCmd
  | bv_ite_merge_then_if : Term -> Term -> Term -> Term -> CCmd
  | bv_ite_merge_else_if : Term -> Term -> Term -> Term -> CCmd
  | bv_ite_merge_then_else : Term -> Term -> Term -> Term -> CCmd
  | bv_ite_merge_else_else : Term -> Term -> Term -> Term -> CCmd
  | bv_shl_by_const_0 : Term -> Term -> CCmd
  | bv_shl_by_const_1 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_shl_by_const_2 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_lshr_by_const_0 : Term -> Term -> CCmd
  | bv_lshr_by_const_1 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_lshr_by_const_2 : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_ashr_by_const_0 : Term -> Term -> CCmd
  | bv_ashr_by_const_1 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_ashr_by_const_2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_and_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_or_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_xor_concat_pullup : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_and_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_or_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_xor_concat_pullup2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_and_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_or_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_xor_concat_pullup3 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_xor_duplicate : Term -> Term -> CIndex -> CCmd
  | bv_xor_ones : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_xor_not : Term -> Term -> CCmd
  | bv_not_idemp : Term -> CCmd
  | bv_ult_zero_1 : Term -> Term -> CCmd
  | bv_ult_zero_2 : Term -> Term -> CCmd
  | bv_ult_self : Term -> CCmd
  | bv_lt_self : Term -> CCmd
  | bv_ule_self : Term -> CCmd
  | bv_ule_zero : Term -> Term -> CCmd
  | bv_zero_ule : Term -> Term -> CCmd
  | bv_sle_self : Term -> CCmd
  | bv_ule_max : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_not_ult : Term -> Term -> CCmd
  | bv_mult_pow2_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_mult_pow2_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_mult_pow2_2b : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_extract_mult_leading_bit : Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_udiv_pow2_not_one : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_udiv_zero : Term -> Term -> CCmd
  | bv_udiv_one : Term -> Term -> CCmd
  | bv_urem_pow2_not_one : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_urem_one : Term -> Term -> CCmd
  | bv_urem_self : Term -> Term -> CIndex -> CCmd
  | bv_shl_zero : Term -> Term -> CCmd
  | bv_lshr_zero : Term -> Term -> CCmd
  | bv_ashr_zero : Term -> Term -> CCmd
  | bv_ugt_urem : Term -> Term -> Term -> CIndex -> CCmd
  | bv_ult_one : Term -> Term -> CIndex -> CCmd
  | bv_merge_sign_extend_1 : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | bv_merge_sign_extend_2 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_eq_const_1 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_eq_const_2 : Term -> Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_zero_extend_eq_const_1 : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_zero_extend_eq_const_2 : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_zero_extend_ult_const_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_zero_extend_ult_const_2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_ult_const_1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_ult_const_2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_ult_const_3 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | bv_sign_extend_ult_const_4 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | sets_eq_singleton_emp : Term -> Term -> Term -> CIndex -> CCmd
  | sets_member_singleton : Term -> Term -> CCmd
  | sets_member_emp : Term -> Term -> Term -> CIndex -> CCmd
  | sets_subset_elim : Term -> Term -> CCmd
  | sets_union_comm : Term -> Term -> CCmd
  | sets_inter_comm : Term -> Term -> CCmd
  | sets_inter_emp1 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_inter_emp2 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_minus_emp1 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_minus_emp2 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_union_emp1 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_union_emp2 : Term -> Term -> Term -> CIndex -> CCmd
  | sets_inter_member : Term -> Term -> Term -> CCmd
  | sets_minus_member : Term -> Term -> Term -> CCmd
  | sets_union_member : Term -> Term -> Term -> CCmd
  | sets_choose_singleton : Term -> CCmd
  | sets_minus_self : Term -> Term -> CCmd
  | sets_is_empty_elim : Term -> Term -> CCmd
  | sets_is_singleton_elim : Term -> CCmd
  | str_eq_ctn_false : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_eq_ctn_full_false1 : Term -> Term -> CIndex -> CCmd
  | str_eq_ctn_full_false2 : Term -> Term -> CIndex -> CCmd
  | str_eq_len_false : Term -> Term -> CIndex -> CCmd
  | str_substr_empty_str : Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_empty_range : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_empty_start : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_empty_start_neg : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_substr_start_geq_len : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_eq_empty : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_substr_z_eq_empty_leq : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_substr_eq_empty_leq_len : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_len_replace_inv : Term -> Term -> Term -> CIndex -> CCmd
  | str_len_replace_all_inv : Term -> Term -> Term -> CIndex -> CCmd
  | str_len_update_inv : Term -> Term -> Term -> CCmd
  | str_update_in_first_concat : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CIndex -> CCmd
  | str_len_substr_in_range : Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_concat_clash : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_concat_clash_rev : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_concat_clash2 : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_concat_clash2_rev : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_concat_unify : Term -> Term -> Term -> Term -> Term -> CCmd
  | str_concat_unify_rev : Term -> Term -> Term -> Term -> Term -> CCmd
  | str_concat_unify_base : Term -> Term -> Term -> Term -> CCmd
  | str_concat_unify_base_rev : Term -> Term -> Term -> Term -> CCmd
  | str_prefixof_elim : Term -> Term -> CCmd
  | str_suffixof_elim : Term -> Term -> CCmd
  | str_prefixof_eq : Term -> Term -> CIndex -> CCmd
  | str_suffixof_eq : Term -> Term -> CIndex -> CCmd
  | str_prefixof_one : Term -> Term -> CIndex -> CCmd
  | str_suffixof_one : Term -> Term -> CIndex -> CCmd
  | str_substr_combine1 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_substr_combine2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_substr_combine3 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_substr_combine4 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_substr_concat1 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_substr_concat2 : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_replace : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_substr_full : Term -> Term -> CIndex -> CCmd
  | str_substr_full_eq : Term -> Term -> CIndex -> CCmd
  | str_contains_refl : Term -> CCmd
  | str_contains_concat_find : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_contains_concat_find_contra : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_contains_split_char : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_contains_leq_len_eq : Term -> Term -> CIndex -> CCmd
  | str_contains_emp : Term -> Term -> CIndex -> CCmd
  | str_contains_char : Term -> Term -> Term -> CIndex -> CCmd
  | str_at_elim : Term -> Term -> CCmd
  | str_replace_self : Term -> Term -> CCmd
  | str_replace_id : Term -> Term -> CCmd
  | str_replace_prefix : Term -> Term -> Term -> Term -> CCmd
  | str_replace_no_contains : Term -> Term -> Term -> CIndex -> CCmd
  | str_replace_find_base : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_replace_find_first_concat : Term -> Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_replace_empty : Term -> Term -> Term -> CIndex -> CCmd
  | str_replace_one_pre : Term -> Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_replace_find_pre : Term -> Term -> Term -> Term -> CCmd
  | str_replace_all_no_contains : Term -> Term -> Term -> CIndex -> CCmd
  | str_replace_all_empty : Term -> Term -> Term -> CIndex -> CCmd
  | str_replace_all_id : Term -> Term -> CCmd
  | str_replace_all_self : Term -> Term -> CIndex -> CCmd
  | str_replace_re_none : Term -> Term -> CCmd
  | str_replace_re_all_none : Term -> Term -> CCmd
  | str_len_concat_rec : Term -> Term -> Term -> CCmd
  | str_len_eq_zero_concat_rec : Term -> Term -> Term -> Term -> CCmd
  | str_len_eq_zero_base : Term -> Term -> CCmd
  | str_indexof_self : Term -> Term -> Term -> CCmd
  | str_indexof_no_contains : Term -> Term -> Term -> CIndex -> CCmd
  | str_indexof_oob : Term -> Term -> Term -> CIndex -> CCmd
  | str_indexof_oob2 : Term -> Term -> Term -> CIndex -> CCmd
  | str_indexof_contains_pre : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_indexof_contains_concat_pre : Term -> Term -> Term -> Term -> CCmd
  | str_indexof_find_emp : Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_indexof_eq_irr : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_indexof_re_none : Term -> Term -> CCmd
  | str_indexof_re_emp_re : Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_to_lower_concat : Term -> Term -> Term -> CCmd
  | str_to_upper_concat : Term -> Term -> Term -> CCmd
  | str_to_lower_upper : Term -> CCmd
  | str_to_upper_lower : Term -> CCmd
  | str_to_lower_len : Term -> CCmd
  | str_to_upper_len : Term -> CCmd
  | str_to_lower_from_int : Term -> CCmd
  | str_to_upper_from_int : Term -> CCmd
  | str_to_int_concat_neg_one : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_is_digit_elim : Term -> CCmd
  | str_leq_empty : Term -> CCmd
  | str_leq_empty_eq : Term -> CCmd
  | str_leq_concat_false : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_leq_concat_true : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | str_leq_concat_base_1 : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_leq_concat_base_2 : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_lt_elim : Term -> Term -> CCmd
  | str_from_int_no_ctn_nondigit : Term -> Term -> CIndex -> CIndex -> CCmd
  | str_substr_ctn_contra : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_ctn : Term -> Term -> Term -> CCmd
  | str_replace_dual_ctn : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_replace_dual_ctn_false : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_replace_self_ctn_simp : Term -> Term -> CCmd
  | str_replace_emp_ctn_src : Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_char_start_eq_len : Term -> Term -> Term -> CIndex -> CCmd
  | str_contains_repl_char : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_contains_repl_self_tgt_char : Term -> Term -> Term -> CIndex -> CCmd
  | str_contains_repl_self : Term -> Term -> CCmd
  | str_contains_repl_tgt : Term -> Term -> Term -> CCmd
  | str_repl_repl_len_id : Term -> Term -> CIndex -> CCmd
  | str_repl_repl_src_tgt_no_ctn : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_repl_repl_tgt_self : Term -> Term -> CCmd
  | str_repl_repl_tgt_no_ctn : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_repl_repl_src_self : Term -> Term -> Term -> CCmd
  | str_repl_repl_src_inv_no_ctn1 : Term -> Term -> Term -> CIndex -> CCmd
  | str_repl_repl_src_inv_no_ctn2 : Term -> Term -> Term -> CIndex -> CCmd
  | str_repl_repl_src_inv_no_ctn3 : Term -> Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_repl_repl_dual_self : Term -> Term -> CCmd
  | str_repl_repl_dual_ite1 : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_repl_repl_dual_ite2 : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_repl_repl_lookahead_id_simp : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | re_all_elim : CCmd
  | re_opt_elim : Term -> CCmd
  | re_diff_elim : Term -> Term -> CCmd
  | re_plus_elim : Term -> CCmd
  | re_repeat_elim : Term -> Term -> CCmd
  | re_concat_star_swap : Term -> Term -> Term -> CCmd
  | re_concat_star_repeat : Term -> Term -> Term -> CCmd
  | re_concat_star_subsume1 : Term -> Term -> Term -> CCmd
  | re_concat_star_subsume2 : Term -> Term -> Term -> CCmd
  | re_concat_merge : Term -> Term -> Term -> Term -> CCmd
  | re_union_all : Term -> Term -> CCmd
  | re_union_const_elim : Term -> Term -> CIndex -> CCmd
  | re_inter_all : Term -> Term -> CCmd
  | re_star_none : CCmd
  | re_star_emp : CCmd
  | re_star_star : Term -> CCmd
  | re_range_refl : Term -> CIndex -> CCmd
  | re_range_emp : Term -> Term -> CIndex -> CIndex -> CIndex -> CCmd
  | re_range_non_singleton_1 : Term -> Term -> CIndex -> CCmd
  | re_range_non_singleton_2 : Term -> Term -> CIndex -> CCmd
  | re_star_union_char : Term -> Term -> CCmd
  | re_star_union_drop_emp : Term -> Term -> CCmd
  | re_loop_neg : Term -> Term -> Term -> CIndex -> CCmd
  | re_inter_cstring : Term -> Term -> Term -> CIndex -> CCmd
  | re_inter_cstring_neg : Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_len_include : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_len_include_pre : Term -> Term -> Term -> Term -> CIndex -> CCmd
  | str_substr_len_norm : Term -> Term -> Term -> CIndex -> CCmd
  | seq_len_rev : Term -> CCmd
  | seq_rev_rev : Term -> CCmd
  | seq_rev_concat : Term -> Term -> Term -> CCmd
  | str_eq_repl_self_emp : Term -> Term -> Term -> CIndex -> CCmd
  | str_eq_repl_no_change : Term -> Term -> Term -> CIndex -> CCmd
  | str_eq_repl_tgt_eq_len : Term -> Term -> Term -> CIndex -> CCmd
  | str_eq_repl_len_one_emp_prefix : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_eq_repl_emp_tgt_nemp : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_eq_repl_nemp_src_emp : Term -> Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_eq_repl_self_src : Term -> Term -> CCmd
  | seq_len_unit : Term -> CCmd
  | seq_nth_unit : Term -> CCmd
  | seq_rev_unit : Term -> CCmd
  | re_in_empty : Term -> CCmd
  | re_in_sigma : Term -> CCmd
  | re_in_sigma_star : Term -> CCmd
  | re_in_cstring : Term -> Term -> CCmd
  | re_in_comp : Term -> Term -> CCmd
  | str_in_re_union_elim : Term -> Term -> Term -> Term -> CCmd
  | str_in_re_inter_elim : Term -> Term -> Term -> Term -> CCmd
  | str_in_re_range_elim : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | str_in_re_contains : Term -> Term -> CCmd
  | str_in_re_from_int_nemp_dig_range : Term -> CIndex -> CCmd
  | str_in_re_from_int_dig_range : Term -> CCmd
  | eq_refl : Term -> CCmd
  | eq_symm : Term -> Term -> CCmd
  | eq_cond_deq : Term -> Term -> Term -> CIndex -> CCmd
  | eq_ite_lift : Term -> Term -> Term -> Term -> CCmd
  | distinct_binary_elim : Term -> Term -> CCmd
  | uf_bv2nat_int2bv : Term -> Term -> CIndex -> CCmd
  | uf_bv2nat_int2bv_extend : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | uf_bv2nat_int2bv_extract : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | uf_int2bv_bv2nat : Term -> Term -> CCmd
  | uf_bv2nat_geq_elim : Term -> Term -> Term -> CIndex -> CCmd
  | uf_int2bv_bvult_equiv : Term -> Term -> CCmd
  | uf_int2bv_bvule_equiv : Term -> Term -> CCmd
  | uf_sbv_to_int_elim : Term -> Term -> Term -> CIndex -> CIndex -> CCmd
  | evaluate : Term -> CCmd
  | distinct_values : Term -> Term -> CCmd
  | aci_norm : Term -> CCmd
  | absorb : Term -> CCmd
  | distinct_card_conflict : Term -> CCmd

deriving Repr, Inhabited

/-
-/
inductive CCmdList : Type where
  | nil : CCmdList
  | cons : CCmd -> CCmdList -> CCmdList
deriving Repr, Inhabited

def __eo_StateObj_proven : CStateObj -> Term
  | (CStateObj.assume F) => F
  | (CStateObj.assume_push F) => F
  | (CStateObj.proven F) => F


def __eo_state_proven_nth : CState -> CIndex -> Term
  | (CState.cons so s), (Term.Numeral 0) => (__eo_StateObj_proven so)
  | (CState.cons so s), n => (__eo_state_proven_nth s (__eo_add n (Term.Numeral (-1 : eo_lit_Int))))
  | s, n => (Term.Boolean true)


def __eo_state_is_closed : CState -> Term
  | (CState.cons (CStateObj.assume_push F) s) => (Term.Boolean false)
  | (CState.cons so s) => (__eo_state_is_closed s)
  | CState.nil => (Term.Boolean true)
  | s => (Term.Boolean false)


def __eo_push_assume : Term -> CState -> CState
  | F, s => (CState.cons (CStateObj.assume_push F) s)


def __eo_push_proven_check : Term -> Term -> CState -> CState
  | (Term.Boolean true), F, s => (CState.cons (CStateObj.proven F) s)
  | b, F, s => CState.Stuck


def __eo_push_proven : Term -> CState -> CState
  | F, s => (__eo_push_proven_check (__eo_is_ok F) F s)


def __eo_mk_premise_list : Term -> CIndexList -> CState -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | f, CIndexList.nil, S => (__eo_nil f Term.Bool)
  | f, (CIndexList.cons n pl), S => (__eo_cons f (__eo_state_proven_nth S n) (__eo_mk_premise_list f pl S))


def __eo_invoke_cmd_pop_scope : CState -> Proof -> CState
  | (CState.cons (CStateObj.assume_push A) s), p1 => (__eo_push_proven (__eo_prog_scope A p1) s)
  | (CState.cons so s), p1 => (__eo_invoke_cmd_pop_scope s p1)
  | s, p1 => CState.Stuck


def __eo_invoke_cmd_check_proven : CState -> Term -> CState
  | (CState.cons (CStateObj.proven F) S), proven => (__eo_push_proven_check (__eo_eq F proven) F S)
  | S, proven => CState.Stuck


def __eo_invoke_cmd (S : CState) : CCmd -> CState
  | (CCmd.assume_push proven) => (__eo_push_assume proven S)
  | (CCmd.check_proven proven) => (__eo_invoke_cmd_check_proven S proven)
  | (CCmd.scope n1) => (__eo_invoke_cmd_pop_scope S (Proof.pf (__eo_state_proven_nth S n1)))
  | (CCmd.process_scope a1 n1) => (__eo_push_proven (__eo_prog_process_scope a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.ite_eq a1) => (__eo_push_proven (__eo_prog_ite_eq a1) S)
  | (CCmd.split a1) => (__eo_push_proven (__eo_prog_split a1) S)
  | (CCmd.resolution a1 a2 n1 n2) => (__eo_push_proven (__eo_prog_resolution a1 a2 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.chain_resolution a1 a2 premises) => (__eo_push_proven (__eo_prog_chain_resolution a1 a2 (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.chain_m_resolution a1 a2 a3 premises) => (__eo_push_proven (__eo_prog_chain_m_resolution a1 a2 a3 (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.factoring n1) => (__eo_push_proven (__eo_prog_factoring (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.reordering a1 n1) => (__eo_push_proven (__eo_prog_reordering a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.eq_resolve n1 n2) => (__eo_push_proven (__eo_prog_eq_resolve (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.modus_ponens n1 n2) => (__eo_push_proven (__eo_prog_modus_ponens (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.not_not_elim n1) => (__eo_push_proven (__eo_prog_not_not_elim (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.contra n1 n2) => (__eo_push_proven (__eo_prog_contra (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.and_elim a1 n1) => (__eo_push_proven (__eo_prog_and_elim a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.and_intro premises) => (__eo_push_proven (__eo_prog_and_intro (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.not_or_elim a1 n1) => (__eo_push_proven (__eo_prog_not_or_elim a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.implies_elim n1) => (__eo_push_proven (__eo_prog_implies_elim (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_implies_elim1 n1) => (__eo_push_proven (__eo_prog_not_implies_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_implies_elim2 n1) => (__eo_push_proven (__eo_prog_not_implies_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.equiv_elim1 n1) => (__eo_push_proven (__eo_prog_equiv_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.equiv_elim2 n1) => (__eo_push_proven (__eo_prog_equiv_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_equiv_elim1 n1) => (__eo_push_proven (__eo_prog_not_equiv_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_equiv_elim2 n1) => (__eo_push_proven (__eo_prog_not_equiv_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.xor_elim1 n1) => (__eo_push_proven (__eo_prog_xor_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.xor_elim2 n1) => (__eo_push_proven (__eo_prog_xor_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_xor_elim1 n1) => (__eo_push_proven (__eo_prog_not_xor_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_xor_elim2 n1) => (__eo_push_proven (__eo_prog_not_xor_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.ite_elim1 n1) => (__eo_push_proven (__eo_prog_ite_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.ite_elim2 n1) => (__eo_push_proven (__eo_prog_ite_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_ite_elim1 n1) => (__eo_push_proven (__eo_prog_not_ite_elim1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_ite_elim2 n1) => (__eo_push_proven (__eo_prog_not_ite_elim2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.not_and n1) => (__eo_push_proven (__eo_prog_not_and (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.cnf_and_pos a1 a2) => (__eo_push_proven (__eo_prog_cnf_and_pos a1 a2) S)
  | (CCmd.cnf_and_neg a1) => (__eo_push_proven (__eo_prog_cnf_and_neg a1) S)
  | (CCmd.cnf_or_pos a1) => (__eo_push_proven (__eo_prog_cnf_or_pos a1) S)
  | (CCmd.cnf_or_neg a1 a2) => (__eo_push_proven (__eo_prog_cnf_or_neg a1 a2) S)
  | (CCmd.cnf_implies_pos a1) => (__eo_push_proven (__eo_prog_cnf_implies_pos a1) S)
  | (CCmd.cnf_implies_neg1 a1) => (__eo_push_proven (__eo_prog_cnf_implies_neg1 a1) S)
  | (CCmd.cnf_implies_neg2 a1) => (__eo_push_proven (__eo_prog_cnf_implies_neg2 a1) S)
  | (CCmd.cnf_equiv_pos1 a1) => (__eo_push_proven (__eo_prog_cnf_equiv_pos1 a1) S)
  | (CCmd.cnf_equiv_pos2 a1) => (__eo_push_proven (__eo_prog_cnf_equiv_pos2 a1) S)
  | (CCmd.cnf_equiv_neg1 a1) => (__eo_push_proven (__eo_prog_cnf_equiv_neg1 a1) S)
  | (CCmd.cnf_equiv_neg2 a1) => (__eo_push_proven (__eo_prog_cnf_equiv_neg2 a1) S)
  | (CCmd.cnf_xor_pos1 a1) => (__eo_push_proven (__eo_prog_cnf_xor_pos1 a1) S)
  | (CCmd.cnf_xor_pos2 a1) => (__eo_push_proven (__eo_prog_cnf_xor_pos2 a1) S)
  | (CCmd.cnf_xor_neg1 a1) => (__eo_push_proven (__eo_prog_cnf_xor_neg1 a1) S)
  | (CCmd.cnf_xor_neg2 a1) => (__eo_push_proven (__eo_prog_cnf_xor_neg2 a1) S)
  | (CCmd.cnf_ite_pos1 a1) => (__eo_push_proven (__eo_prog_cnf_ite_pos1 a1) S)
  | (CCmd.cnf_ite_pos2 a1) => (__eo_push_proven (__eo_prog_cnf_ite_pos2 a1) S)
  | (CCmd.cnf_ite_pos3 a1) => (__eo_push_proven (__eo_prog_cnf_ite_pos3 a1) S)
  | (CCmd.cnf_ite_neg1 a1) => (__eo_push_proven (__eo_prog_cnf_ite_neg1 a1) S)
  | (CCmd.cnf_ite_neg2 a1) => (__eo_push_proven (__eo_prog_cnf_ite_neg2 a1) S)
  | (CCmd.cnf_ite_neg3 a1) => (__eo_push_proven (__eo_prog_cnf_ite_neg3 a1) S)
  | (CCmd.arrays_read_over_write a1 n1) => (__eo_push_proven (__eo_prog_arrays_read_over_write a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arrays_read_over_write_contra n1) => (__eo_push_proven (__eo_prog_arrays_read_over_write_contra (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arrays_read_over_write_1 a1) => (__eo_push_proven (__eo_prog_arrays_read_over_write_1 a1) S)
  | (CCmd.arrays_ext n1) => (__eo_push_proven (__eo_prog_arrays_ext (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.refl a1) => (__eo_push_proven (__eo_prog_refl a1) S)
  | (CCmd.symm n1) => (__eo_push_proven (__eo_prog_symm (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.trans premises) => (__eo_push_proven (__eo_prog_trans (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.cong a1 premises) => (__eo_push_proven (__eo_prog_cong a1 (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.nary_cong a1 premises) => (__eo_push_proven (__eo_prog_nary_cong a1 (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.pairwise_cong a1 premises) => (__eo_push_proven (__eo_prog_pairwise_cong a1 (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.true_intro n1) => (__eo_push_proven (__eo_prog_true_intro (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.true_elim n1) => (__eo_push_proven (__eo_prog_true_elim (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.false_intro n1) => (__eo_push_proven (__eo_prog_false_intro (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.false_elim n1) => (__eo_push_proven (__eo_prog_false_elim (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.ho_cong premises) => (__eo_push_proven (__eo_prog_ho_cong (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.distinct_elim a1) => (__eo_push_proven (__eo_prog_distinct_elim a1) S)
  | (CCmd.distinct_true a1) => (__eo_push_proven (__eo_prog_distinct_true a1) S)
  | (CCmd.distinct_false a1) => (__eo_push_proven (__eo_prog_distinct_false a1) S)
  | (CCmd.lambda_elim a1) => (__eo_push_proven (__eo_prog_lambda_elim a1) S)
  | (CCmd.arith_sum_ub premises) => (__eo_push_proven (__eo_prog_arith_sum_ub (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.arith_mult_pos a1 a2) => (__eo_push_proven (__eo_prog_arith_mult_pos a1 a2) S)
  | (CCmd.arith_mult_neg a1 a2) => (__eo_push_proven (__eo_prog_arith_mult_neg a1 a2) S)
  | (CCmd.arith_trichotomy n1 n2) => (__eo_push_proven (__eo_prog_arith_trichotomy (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.int_tight_ub n1) => (__eo_push_proven (__eo_prog_int_tight_ub (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.int_tight_lb n1) => (__eo_push_proven (__eo_prog_int_tight_lb (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_mult_tangent a1 a2 a3 a4 a5) => (__eo_push_proven (__eo_prog_arith_mult_tangent a1 a2 a3 a4 a5) S)
  | (CCmd.arith_mult_sign a1 a2) => (__eo_push_proven (__eo_prog_arith_mult_sign a1 a2) S)
  | (CCmd.arith_mult_abs_comparison premises) => (__eo_push_proven (__eo_prog_arith_mult_abs_comparison (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.arith_reduction a1) => (__eo_push_proven (__eo_prog_arith_reduction a1) S)
  | (CCmd.arith_poly_norm a1) => (__eo_push_proven (__eo_prog_arith_poly_norm a1) S)
  | (CCmd.arith_poly_norm_rel a1 n1) => (__eo_push_proven (__eo_prog_arith_poly_norm_rel a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_repeat_elim a1) => (__eo_push_proven (__eo_prog_bv_repeat_elim a1) S)
  | (CCmd.bv_smulo_elim a1) => (__eo_push_proven (__eo_prog_bv_smulo_elim a1) S)
  | (CCmd.bv_umulo_elim a1) => (__eo_push_proven (__eo_prog_bv_umulo_elim a1) S)
  | (CCmd.bv_bitwise_slicing a1) => (__eo_push_proven (__eo_prog_bv_bitwise_slicing a1) S)
  | (CCmd.bv_bitblast_step a1) => (__eo_push_proven (__eo_prog_bv_bitblast_step a1) S)
  | (CCmd.bv_poly_norm a1) => (__eo_push_proven (__eo_prog_bv_poly_norm a1) S)
  | (CCmd.bv_poly_norm_eq a1 n1) => (__eo_push_proven (__eo_prog_bv_poly_norm_eq a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.string_length_pos a1) => (__eo_push_proven (__eo_prog_string_length_pos a1) S)
  | (CCmd.string_length_non_empty n1) => (__eo_push_proven (__eo_prog_string_length_non_empty (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.concat_eq a1 n1) => (__eo_push_proven (__eo_prog_concat_eq a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.concat_unify a1 n1 n2) => (__eo_push_proven (__eo_prog_concat_unify a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.concat_csplit a1 n1 n2) => (__eo_push_proven (__eo_prog_concat_csplit a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.concat_split a1 n1 n2) => (__eo_push_proven (__eo_prog_concat_split a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.concat_lprop a1 n1 n2) => (__eo_push_proven (__eo_prog_concat_lprop a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.concat_cprop a1 n1 n2) => (__eo_push_proven (__eo_prog_concat_cprop a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.string_decompose a1 n1 n2) => (__eo_push_proven (__eo_prog_string_decompose a1 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.exists_string_length a1 a2 a3) => (__eo_push_proven (__eo_prog_exists_string_length a1 a2 a3) S)
  | (CCmd.string_code_inj a1 a2) => (__eo_push_proven (__eo_prog_string_code_inj a1 a2) S)
  | (CCmd.string_seq_unit_inj n1) => (__eo_push_proven (__eo_prog_string_seq_unit_inj (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_inter n1 n2) => (__eo_push_proven (__eo_prog_re_inter (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.re_concat premises) => (__eo_push_proven (__eo_prog_re_concat (Proof.pf (__eo_mk_premise_list Term.and premises S))) S)
  | (CCmd.re_unfold_pos n1) => (__eo_push_proven (__eo_prog_re_unfold_pos (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_unfold_neg_concat_fixed a1 n1) => (__eo_push_proven (__eo_prog_re_unfold_neg_concat_fixed a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_unfold_neg n1) => (__eo_push_proven (__eo_prog_re_unfold_neg (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.string_ext n1) => (__eo_push_proven (__eo_prog_string_ext (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.string_reduction a1) => (__eo_push_proven (__eo_prog_string_reduction a1) S)
  | (CCmd.string_eager_reduction a1) => (__eo_push_proven (__eo_prog_string_eager_reduction a1) S)
  | (CCmd.arith_string_pred_entail a1) => (__eo_push_proven (__eo_prog_arith_string_pred_entail a1) S)
  | (CCmd.arith_string_pred_safe_approx a1) => (__eo_push_proven (__eo_prog_arith_string_pred_safe_approx a1) S)
  | (CCmd.str_in_re_eval a1) => (__eo_push_proven (__eo_prog_str_in_re_eval a1) S)
  | (CCmd.str_in_re_consume a1) => (__eo_push_proven (__eo_prog_str_in_re_consume a1) S)
  | (CCmd.re_loop_elim a1) => (__eo_push_proven (__eo_prog_re_loop_elim a1) S)
  | (CCmd.re_eq_elim a1) => (__eo_push_proven (__eo_prog_re_eq_elim a1) S)
  | (CCmd.re_inter_inclusion a1) => (__eo_push_proven (__eo_prog_re_inter_inclusion a1) S)
  | (CCmd.re_union_inclusion a1) => (__eo_push_proven (__eo_prog_re_union_inclusion a1) S)
  | (CCmd.str_in_re_concat_star_char a1) => (__eo_push_proven (__eo_prog_str_in_re_concat_star_char a1) S)
  | (CCmd.str_in_re_sigma a1) => (__eo_push_proven (__eo_prog_str_in_re_sigma a1) S)
  | (CCmd.str_in_re_sigma_star a1) => (__eo_push_proven (__eo_prog_str_in_re_sigma_star a1) S)
  | (CCmd.str_ctn_multiset_subset a1) => (__eo_push_proven (__eo_prog_str_ctn_multiset_subset a1) S)
  | (CCmd.str_overlap_split_ctn a1) => (__eo_push_proven (__eo_prog_str_overlap_split_ctn a1) S)
  | (CCmd.str_overlap_endpoints_ctn a1) => (__eo_push_proven (__eo_prog_str_overlap_endpoints_ctn a1) S)
  | (CCmd.str_overlap_endpoints_indexof a1) => (__eo_push_proven (__eo_prog_str_overlap_endpoints_indexof a1) S)
  | (CCmd.str_overlap_endpoints_replace a1) => (__eo_push_proven (__eo_prog_str_overlap_endpoints_replace a1) S)
  | (CCmd.str_indexof_re_eval a1) => (__eo_push_proven (__eo_prog_str_indexof_re_eval a1) S)
  | (CCmd.str_replace_re_eval a1) => (__eo_push_proven (__eo_prog_str_replace_re_eval a1) S)
  | (CCmd.str_replace_re_all_eval a1) => (__eo_push_proven (__eo_prog_str_replace_re_all_eval a1) S)
  | (CCmd.seq_eval_op a1) => (__eo_push_proven (__eo_prog_seq_eval_op a1) S)
  | (CCmd.sets_singleton_inj n1) => (__eo_push_proven (__eo_prog_sets_singleton_inj (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_ext n1) => (__eo_push_proven (__eo_prog_sets_ext (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_eval_op a1) => (__eo_push_proven (__eo_prog_sets_eval_op a1) S)
  | (CCmd.sets_insert_elim a1) => (__eo_push_proven (__eo_prog_sets_insert_elim a1) S)
  | (CCmd.ubv_to_int_elim a1) => (__eo_push_proven (__eo_prog_ubv_to_int_elim a1) S)
  | (CCmd.int_to_bv_elim a1) => (__eo_push_proven (__eo_prog_int_to_bv_elim a1) S)
  | (CCmd.instantiate a1 n1) => (__eo_push_proven (__eo_prog_instantiate a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.skolemize n1) => (__eo_push_proven (__eo_prog_skolemize (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.skolem_intro a1) => (__eo_push_proven (__eo_prog_skolem_intro a1) S)
  | (CCmd.alpha_equiv a1 a2 a3) => (__eo_push_proven (__eo_prog_alpha_equiv a1 a2 a3) S)
  | (CCmd.beta_reduce a1) => (__eo_push_proven (__eo_prog_beta_reduce a1) S)
  | (CCmd.quant_var_reordering a1) => (__eo_push_proven (__eo_prog_quant_var_reordering a1) S)
  | (CCmd.exists_elim a1) => (__eo_push_proven (__eo_prog_exists_elim a1) S)
  | (CCmd.quant_unused_vars a1) => (__eo_push_proven (__eo_prog_quant_unused_vars a1) S)
  | (CCmd.quant_merge_prenex a1) => (__eo_push_proven (__eo_prog_quant_merge_prenex a1) S)
  | (CCmd.quant_miniscope_and a1) => (__eo_push_proven (__eo_prog_quant_miniscope_and a1) S)
  | (CCmd.quant_miniscope_or a1) => (__eo_push_proven (__eo_prog_quant_miniscope_or a1) S)
  | (CCmd.quant_miniscope_ite a1) => (__eo_push_proven (__eo_prog_quant_miniscope_ite a1) S)
  | (CCmd.quant_var_elim_eq a1) => (__eo_push_proven (__eo_prog_quant_var_elim_eq a1) S)
  | (CCmd.quant_dt_split a1) => (__eo_push_proven (__eo_prog_quant_dt_split a1) S)
  | (CCmd.dt_split a1) => (__eo_push_proven (__eo_prog_dt_split a1) S)
  | (CCmd.dt_inst a1) => (__eo_push_proven (__eo_prog_dt_inst a1) S)
  | (CCmd.dt_collapse_selector a1) => (__eo_push_proven (__eo_prog_dt_collapse_selector a1) S)
  | (CCmd.dt_collapse_tester a1) => (__eo_push_proven (__eo_prog_dt_collapse_tester a1) S)
  | (CCmd.dt_collapse_tester_singleton a1) => (__eo_push_proven (__eo_prog_dt_collapse_tester_singleton a1) S)
  | (CCmd.dt_cons_eq a1) => (__eo_push_proven (__eo_prog_dt_cons_eq a1) S)
  | (CCmd.dt_cons_eq_clash a1) => (__eo_push_proven (__eo_prog_dt_cons_eq_clash a1) S)
  | (CCmd.dt_cycle a1) => (__eo_push_proven (__eo_prog_dt_cycle a1) S)
  | (CCmd.dt_collapse_updater a1) => (__eo_push_proven (__eo_prog_dt_collapse_updater a1) S)
  | (CCmd.dt_updater_elim a1) => (__eo_push_proven (__eo_prog_dt_updater_elim a1) S)
  | (CCmd.arith_div_total_zero_real a1) => (__eo_push_proven (__eo_prog_arith_div_total_zero_real a1) S)
  | (CCmd.arith_div_total_zero_int a1) => (__eo_push_proven (__eo_prog_arith_div_total_zero_int a1) S)
  | (CCmd.arith_int_div_total a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_int_div_total a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_int_div_total_one a1) => (__eo_push_proven (__eo_prog_arith_int_div_total_one a1) S)
  | (CCmd.arith_int_div_total_zero a1) => (__eo_push_proven (__eo_prog_arith_int_div_total_zero a1) S)
  | (CCmd.arith_int_div_total_neg a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_int_div_total_neg a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_int_mod_total a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_int_mod_total a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_int_mod_total_one a1) => (__eo_push_proven (__eo_prog_arith_int_mod_total_one a1) S)
  | (CCmd.arith_int_mod_total_zero a1) => (__eo_push_proven (__eo_prog_arith_int_mod_total_zero a1) S)
  | (CCmd.arith_int_mod_total_neg a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_int_mod_total_neg a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_elim_gt a1 a2) => (__eo_push_proven (__eo_prog_arith_elim_gt a1 a2) S)
  | (CCmd.arith_elim_lt a1 a2) => (__eo_push_proven (__eo_prog_arith_elim_lt a1 a2) S)
  | (CCmd.arith_elim_int_gt a1 a2) => (__eo_push_proven (__eo_prog_arith_elim_int_gt a1 a2) S)
  | (CCmd.arith_elim_int_lt a1 a2) => (__eo_push_proven (__eo_prog_arith_elim_int_lt a1 a2) S)
  | (CCmd.arith_elim_leq a1 a2) => (__eo_push_proven (__eo_prog_arith_elim_leq a1 a2) S)
  | (CCmd.arith_leq_norm a1 a2) => (__eo_push_proven (__eo_prog_arith_leq_norm a1 a2) S)
  | (CCmd.arith_geq_tighten a1 a2) => (__eo_push_proven (__eo_prog_arith_geq_tighten a1 a2) S)
  | (CCmd.arith_geq_norm1_int a1 a2) => (__eo_push_proven (__eo_prog_arith_geq_norm1_int a1 a2) S)
  | (CCmd.arith_geq_norm1_real a1 a2) => (__eo_push_proven (__eo_prog_arith_geq_norm1_real a1 a2) S)
  | (CCmd.arith_eq_elim_real a1 a2) => (__eo_push_proven (__eo_prog_arith_eq_elim_real a1 a2) S)
  | (CCmd.arith_eq_elim_int a1 a2) => (__eo_push_proven (__eo_prog_arith_eq_elim_int a1 a2) S)
  | (CCmd.arith_to_int_elim a1) => (__eo_push_proven (__eo_prog_arith_to_int_elim a1) S)
  | (CCmd.arith_to_int_elim_to_real a1) => (__eo_push_proven (__eo_prog_arith_to_int_elim_to_real a1) S)
  | (CCmd.arith_div_elim_to_real1 a1 a2) => (__eo_push_proven (__eo_prog_arith_div_elim_to_real1 a1 a2) S)
  | (CCmd.arith_div_elim_to_real2 a1 a2) => (__eo_push_proven (__eo_prog_arith_div_elim_to_real2 a1 a2) S)
  | (CCmd.arith_mod_over_mod_1 a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_mod_over_mod_1 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_mod_over_mod a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_arith_mod_over_mod a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_mod_over_mod_mult a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_arith_mod_over_mod_mult a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_int_eq_conflict a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_int_eq_conflict a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_int_geq_tighten a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_arith_int_geq_tighten a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.arith_divisible_elim a1 a2 n1) => (__eo_push_proven (__eo_prog_arith_divisible_elim a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.arith_abs_eq a1 a2) => (__eo_push_proven (__eo_prog_arith_abs_eq a1 a2) S)
  | (CCmd.arith_abs_int_gt a1 a2) => (__eo_push_proven (__eo_prog_arith_abs_int_gt a1 a2) S)
  | (CCmd.arith_abs_real_gt a1 a2) => (__eo_push_proven (__eo_prog_arith_abs_real_gt a1 a2) S)
  | (CCmd.arith_geq_ite_lift a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_arith_geq_ite_lift a1 a2 a3 a4) S)
  | (CCmd.arith_leq_ite_lift a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_arith_leq_ite_lift a1 a2 a3 a4) S)
  | (CCmd.arith_min_lt1 a1 a2) => (__eo_push_proven (__eo_prog_arith_min_lt1 a1 a2) S)
  | (CCmd.arith_min_lt2 a1 a2) => (__eo_push_proven (__eo_prog_arith_min_lt2 a1 a2) S)
  | (CCmd.arith_max_geq1 a1 a2) => (__eo_push_proven (__eo_prog_arith_max_geq1 a1 a2) S)
  | (CCmd.arith_max_geq2 a1 a2) => (__eo_push_proven (__eo_prog_arith_max_geq2 a1 a2) S)
  | (CCmd.array_read_over_write a1 a2 a3) => (__eo_push_proven (__eo_prog_array_read_over_write a1 a2 a3) S)
  | (CCmd.array_read_over_write2 a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_array_read_over_write2 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.array_store_overwrite a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_array_store_overwrite a1 a2 a3 a4) S)
  | (CCmd.array_store_self a1 a2) => (__eo_push_proven (__eo_prog_array_store_self a1 a2) S)
  | (CCmd.array_read_over_write_split a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_array_read_over_write_split a1 a2 a3 a4) S)
  | (CCmd.array_store_swap a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_array_store_swap a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bool_double_not_elim a1) => (__eo_push_proven (__eo_prog_bool_double_not_elim a1) S)
  | (CCmd.bool_not_true a1 n1) => (__eo_push_proven (__eo_prog_bool_not_true a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bool_not_false a1 n1) => (__eo_push_proven (__eo_prog_bool_not_false a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bool_eq_true a1) => (__eo_push_proven (__eo_prog_bool_eq_true a1) S)
  | (CCmd.bool_eq_false a1) => (__eo_push_proven (__eo_prog_bool_eq_false a1) S)
  | (CCmd.bool_eq_nrefl a1) => (__eo_push_proven (__eo_prog_bool_eq_nrefl a1) S)
  | (CCmd.bool_impl_false1 a1) => (__eo_push_proven (__eo_prog_bool_impl_false1 a1) S)
  | (CCmd.bool_impl_false2 a1) => (__eo_push_proven (__eo_prog_bool_impl_false2 a1) S)
  | (CCmd.bool_impl_true1 a1) => (__eo_push_proven (__eo_prog_bool_impl_true1 a1) S)
  | (CCmd.bool_impl_true2 a1) => (__eo_push_proven (__eo_prog_bool_impl_true2 a1) S)
  | (CCmd.bool_impl_elim a1 a2) => (__eo_push_proven (__eo_prog_bool_impl_elim a1 a2) S)
  | (CCmd.bool_dual_impl_eq a1 a2) => (__eo_push_proven (__eo_prog_bool_dual_impl_eq a1 a2) S)
  | (CCmd.bool_and_conf a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bool_and_conf a1 a2 a3 a4) S)
  | (CCmd.bool_and_conf2 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bool_and_conf2 a1 a2 a3 a4) S)
  | (CCmd.bool_or_taut a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bool_or_taut a1 a2 a3 a4) S)
  | (CCmd.bool_or_taut2 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bool_or_taut2 a1 a2 a3 a4) S)
  | (CCmd.bool_or_de_morgan a1 a2 a3) => (__eo_push_proven (__eo_prog_bool_or_de_morgan a1 a2 a3) S)
  | (CCmd.bool_implies_de_morgan a1 a2) => (__eo_push_proven (__eo_prog_bool_implies_de_morgan a1 a2) S)
  | (CCmd.bool_and_de_morgan a1 a2 a3) => (__eo_push_proven (__eo_prog_bool_and_de_morgan a1 a2 a3) S)
  | (CCmd.bool_or_and_distrib a1 a2 a3 a4 a5) => (__eo_push_proven (__eo_prog_bool_or_and_distrib a1 a2 a3 a4 a5) S)
  | (CCmd.bool_implies_or_distrib a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bool_implies_or_distrib a1 a2 a3 a4) S)
  | (CCmd.bool_xor_refl a1) => (__eo_push_proven (__eo_prog_bool_xor_refl a1) S)
  | (CCmd.bool_xor_nrefl a1) => (__eo_push_proven (__eo_prog_bool_xor_nrefl a1) S)
  | (CCmd.bool_xor_false a1) => (__eo_push_proven (__eo_prog_bool_xor_false a1) S)
  | (CCmd.bool_xor_true a1) => (__eo_push_proven (__eo_prog_bool_xor_true a1) S)
  | (CCmd.bool_xor_comm a1 a2) => (__eo_push_proven (__eo_prog_bool_xor_comm a1 a2) S)
  | (CCmd.bool_xor_elim a1 a2) => (__eo_push_proven (__eo_prog_bool_xor_elim a1 a2) S)
  | (CCmd.bool_not_xor_elim a1 a2) => (__eo_push_proven (__eo_prog_bool_not_xor_elim a1 a2) S)
  | (CCmd.bool_not_eq_elim1 a1 a2) => (__eo_push_proven (__eo_prog_bool_not_eq_elim1 a1 a2) S)
  | (CCmd.bool_not_eq_elim2 a1 a2) => (__eo_push_proven (__eo_prog_bool_not_eq_elim2 a1 a2) S)
  | (CCmd.ite_neg_branch a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_ite_neg_branch a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.ite_then_true a1 a2) => (__eo_push_proven (__eo_prog_ite_then_true a1 a2) S)
  | (CCmd.ite_else_false a1 a2) => (__eo_push_proven (__eo_prog_ite_else_false a1 a2) S)
  | (CCmd.ite_then_false a1 a2) => (__eo_push_proven (__eo_prog_ite_then_false a1 a2) S)
  | (CCmd.ite_else_true a1 a2) => (__eo_push_proven (__eo_prog_ite_else_true a1 a2) S)
  | (CCmd.ite_then_lookahead_self a1 a2) => (__eo_push_proven (__eo_prog_ite_then_lookahead_self a1 a2) S)
  | (CCmd.ite_else_lookahead_self a1 a2) => (__eo_push_proven (__eo_prog_ite_else_lookahead_self a1 a2) S)
  | (CCmd.ite_then_lookahead_not_self a1 a2) => (__eo_push_proven (__eo_prog_ite_then_lookahead_not_self a1 a2) S)
  | (CCmd.ite_else_lookahead_not_self a1 a2) => (__eo_push_proven (__eo_prog_ite_else_lookahead_not_self a1 a2) S)
  | (CCmd.ite_expand a1 a2 a3) => (__eo_push_proven (__eo_prog_ite_expand a1 a2 a3) S)
  | (CCmd.bool_not_ite_elim a1 a2 a3) => (__eo_push_proven (__eo_prog_bool_not_ite_elim a1 a2 a3) S)
  | (CCmd.ite_true_cond a1 a2) => (__eo_push_proven (__eo_prog_ite_true_cond a1 a2) S)
  | (CCmd.ite_false_cond a1 a2) => (__eo_push_proven (__eo_prog_ite_false_cond a1 a2) S)
  | (CCmd.ite_not_cond a1 a2 a3) => (__eo_push_proven (__eo_prog_ite_not_cond a1 a2 a3) S)
  | (CCmd.ite_eq_branch a1 a2) => (__eo_push_proven (__eo_prog_ite_eq_branch a1 a2) S)
  | (CCmd.ite_then_lookahead a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_ite_then_lookahead a1 a2 a3 a4) S)
  | (CCmd.ite_else_lookahead a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_ite_else_lookahead a1 a2 a3 a4) S)
  | (CCmd.ite_then_neg_lookahead a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_ite_then_neg_lookahead a1 a2 a3 a4) S)
  | (CCmd.ite_else_neg_lookahead a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_ite_else_neg_lookahead a1 a2 a3 a4) S)
  | (CCmd.bv_concat_extract_merge a1 a2 a3 a4 a5 a6 a7 n1) => (__eo_push_proven (__eo_prog_bv_concat_extract_merge a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_extract_extract a1 a2 a3 a4 a5 a6 a7 n1 n2) => (__eo_push_proven (__eo_prog_bv_extract_extract a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_extract_whole a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_extract_whole a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_extract_concat_1 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_extract_concat_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_extract_concat_2 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_extract_concat_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_extract_concat_3 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_extract_concat_3 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_extract_concat_4 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_extract_concat_4 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_eq_extract_elim1 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3 n4 n5) => (__eo_push_proven (__eo_prog_bv_eq_extract_elim1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4)) (Proof.pf (__eo_state_proven_nth S n5))) S)
  | (CCmd.bv_eq_extract_elim2 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_eq_extract_elim2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_eq_extract_elim3 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_eq_extract_elim3 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_extract_not a1 a2 a3) => (__eo_push_proven (__eo_prog_bv_extract_not a1 a2 a3) S)
  | (CCmd.bv_extract_sign_extend_1 a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_bv_extract_sign_extend_1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_extract_sign_extend_2 a1 a2 a3 a4 a5 a6 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_extract_sign_extend_2 a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_extract_sign_extend_3 a1 a2 a3 a4 a5 a6 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_extract_sign_extend_3 a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_not_xor a1 a2 a3) => (__eo_push_proven (__eo_prog_bv_not_xor a1 a2 a3) S)
  | (CCmd.bv_and_simplify_1 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_and_simplify_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_and_simplify_2 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_and_simplify_2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_or_simplify_1 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_or_simplify_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_or_simplify_2 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_bv_or_simplify_2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_xor_simplify_1 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_xor_simplify_1 a1 a2 a3 a4) S)
  | (CCmd.bv_xor_simplify_2 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_xor_simplify_2 a1 a2 a3 a4) S)
  | (CCmd.bv_xor_simplify_3 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_xor_simplify_3 a1 a2 a3 a4) S)
  | (CCmd.bv_ult_add_one a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_bv_ult_add_one a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_mult_slt_mult_1 a1 a2 a3 a4 a5 a6 a7 n1 n2) => (__eo_push_proven (__eo_prog_bv_mult_slt_mult_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_mult_slt_mult_2 a1 a2 a3 a4 a5 a6 a7 n1 n2) => (__eo_push_proven (__eo_prog_bv_mult_slt_mult_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_commutative_xor a1 a2) => (__eo_push_proven (__eo_prog_bv_commutative_xor a1 a2) S)
  | (CCmd.bv_commutative_comp a1 a2) => (__eo_push_proven (__eo_prog_bv_commutative_comp a1 a2) S)
  | (CCmd.bv_zero_extend_eliminate_0 a1) => (__eo_push_proven (__eo_prog_bv_zero_extend_eliminate_0 a1) S)
  | (CCmd.bv_sign_extend_eliminate_0 a1) => (__eo_push_proven (__eo_prog_bv_sign_extend_eliminate_0 a1) S)
  | (CCmd.bv_not_neq a1 n1) => (__eo_push_proven (__eo_prog_bv_not_neq a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_ult_ones a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_ult_ones a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_concat_merge_const a1 a2 a3 a4 a5 a6 a7 n1) => (__eo_push_proven (__eo_prog_bv_concat_merge_const a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_commutative_add a1 a2) => (__eo_push_proven (__eo_prog_bv_commutative_add a1 a2) S)
  | (CCmd.bv_sub_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_sub_eliminate a1 a2) S)
  | (CCmd.bv_ite_width_one a1) => (__eo_push_proven (__eo_prog_bv_ite_width_one a1) S)
  | (CCmd.bv_ite_width_one_not a1) => (__eo_push_proven (__eo_prog_bv_ite_width_one_not a1) S)
  | (CCmd.bv_eq_xor_solve a1 a2 a3) => (__eo_push_proven (__eo_prog_bv_eq_xor_solve a1 a2 a3) S)
  | (CCmd.bv_eq_not_solve a1 a2) => (__eo_push_proven (__eo_prog_bv_eq_not_solve a1 a2) S)
  | (CCmd.bv_ugt_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_ugt_eliminate a1 a2) S)
  | (CCmd.bv_uge_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_uge_eliminate a1 a2) S)
  | (CCmd.bv_sgt_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_sgt_eliminate a1 a2) S)
  | (CCmd.bv_sge_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_sge_eliminate a1 a2) S)
  | (CCmd.bv_sle_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_sle_eliminate a1 a2) S)
  | (CCmd.bv_redor_eliminate a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_redor_eliminate a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_redand_eliminate a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_redand_eliminate a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_ule_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_ule_eliminate a1 a2) S)
  | (CCmd.bv_comp_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_comp_eliminate a1 a2) S)
  | (CCmd.bv_rotate_left_eliminate_1 a1 a2 a3 a4 a5 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_rotate_left_eliminate_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_rotate_left_eliminate_2 a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_rotate_left_eliminate_2 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_rotate_right_eliminate_1 a1 a2 a3 a4 a5 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_rotate_right_eliminate_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_rotate_right_eliminate_2 a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_rotate_right_eliminate_2 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_nand_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_nand_eliminate a1 a2) S)
  | (CCmd.bv_nor_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_nor_eliminate a1 a2) S)
  | (CCmd.bv_xnor_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_xnor_eliminate a1 a2) S)
  | (CCmd.bv_sdiv_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_sdiv_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_zero_extend_eliminate a1 a2) => (__eo_push_proven (__eo_prog_bv_zero_extend_eliminate a1 a2) S)
  | (CCmd.bv_uaddo_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_uaddo_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_saddo_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_saddo_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_sdivo_eliminate a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_sdivo_eliminate a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_smod_eliminate a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_smod_eliminate a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_srem_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_srem_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_usubo_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_usubo_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_ssubo_eliminate a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_ssubo_eliminate a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_nego_eliminate a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_nego_eliminate a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_ite_equal_children a1 a2) => (__eo_push_proven (__eo_prog_bv_ite_equal_children a1 a2) S)
  | (CCmd.bv_ite_const_children_1 a1) => (__eo_push_proven (__eo_prog_bv_ite_const_children_1 a1) S)
  | (CCmd.bv_ite_const_children_2 a1) => (__eo_push_proven (__eo_prog_bv_ite_const_children_2 a1) S)
  | (CCmd.bv_ite_equal_cond_1 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_equal_cond_1 a1 a2 a3 a4) S)
  | (CCmd.bv_ite_equal_cond_2 a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_equal_cond_2 a1 a2 a3 a4) S)
  | (CCmd.bv_ite_equal_cond_3 a1 a2 a3 a4 a5) => (__eo_push_proven (__eo_prog_bv_ite_equal_cond_3 a1 a2 a3 a4 a5) S)
  | (CCmd.bv_ite_merge_then_if a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_merge_then_if a1 a2 a3 a4) S)
  | (CCmd.bv_ite_merge_else_if a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_merge_else_if a1 a2 a3 a4) S)
  | (CCmd.bv_ite_merge_then_else a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_merge_then_else a1 a2 a3 a4) S)
  | (CCmd.bv_ite_merge_else_else a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_bv_ite_merge_else_else a1 a2 a3 a4) S)
  | (CCmd.bv_shl_by_const_0 a1 a2) => (__eo_push_proven (__eo_prog_bv_shl_by_const_0 a1 a2) S)
  | (CCmd.bv_shl_by_const_1 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_shl_by_const_1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_shl_by_const_2 a1 a2 a3 a4 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_shl_by_const_2 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_lshr_by_const_0 a1 a2) => (__eo_push_proven (__eo_prog_bv_lshr_by_const_0 a1 a2) S)
  | (CCmd.bv_lshr_by_const_1 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_lshr_by_const_1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_lshr_by_const_2 a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_bv_lshr_by_const_2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_ashr_by_const_0 a1 a2) => (__eo_push_proven (__eo_prog_bv_ashr_by_const_0 a1 a2) S)
  | (CCmd.bv_ashr_by_const_1 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_ashr_by_const_1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_ashr_by_const_2 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_ashr_by_const_2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_and_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_and_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_or_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_or_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_xor_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_xor_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_and_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_and_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_or_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_or_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_xor_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_xor_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_and_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 n1 n2 n3 n4 n5) => (__eo_push_proven (__eo_prog_bv_and_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4)) (Proof.pf (__eo_state_proven_nth S n5))) S)
  | (CCmd.bv_or_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 n1 n2 n3 n4 n5) => (__eo_push_proven (__eo_prog_bv_or_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4)) (Proof.pf (__eo_state_proven_nth S n5))) S)
  | (CCmd.bv_xor_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 n1 n2 n3 n4 n5) => (__eo_push_proven (__eo_prog_bv_xor_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4)) (Proof.pf (__eo_state_proven_nth S n5))) S)
  | (CCmd.bv_xor_duplicate a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_xor_duplicate a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_xor_ones a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_bv_xor_ones a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_xor_not a1 a2) => (__eo_push_proven (__eo_prog_bv_xor_not a1 a2) S)
  | (CCmd.bv_not_idemp a1) => (__eo_push_proven (__eo_prog_bv_not_idemp a1) S)
  | (CCmd.bv_ult_zero_1 a1 a2) => (__eo_push_proven (__eo_prog_bv_ult_zero_1 a1 a2) S)
  | (CCmd.bv_ult_zero_2 a1 a2) => (__eo_push_proven (__eo_prog_bv_ult_zero_2 a1 a2) S)
  | (CCmd.bv_ult_self a1) => (__eo_push_proven (__eo_prog_bv_ult_self a1) S)
  | (CCmd.bv_lt_self a1) => (__eo_push_proven (__eo_prog_bv_lt_self a1) S)
  | (CCmd.bv_ule_self a1) => (__eo_push_proven (__eo_prog_bv_ule_self a1) S)
  | (CCmd.bv_ule_zero a1 a2) => (__eo_push_proven (__eo_prog_bv_ule_zero a1 a2) S)
  | (CCmd.bv_zero_ule a1 a2) => (__eo_push_proven (__eo_prog_bv_zero_ule a1 a2) S)
  | (CCmd.bv_sle_self a1) => (__eo_push_proven (__eo_prog_bv_sle_self a1) S)
  | (CCmd.bv_ule_max a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_bv_ule_max a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_not_ult a1 a2) => (__eo_push_proven (__eo_prog_bv_not_ult a1 a2) S)
  | (CCmd.bv_mult_pow2_1 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_mult_pow2_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_mult_pow2_2 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_mult_pow2_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_mult_pow2_2b a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_mult_pow2_2b a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_extract_mult_leading_bit a1 a2 a3 a4 a5 a6 a7 a8 a9 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_extract_mult_leading_bit a1 a2 a3 a4 a5 a6 a7 a8 a9 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_udiv_pow2_not_one a1 a2 a3 a4 a5 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_udiv_pow2_not_one a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_udiv_zero a1 a2) => (__eo_push_proven (__eo_prog_bv_udiv_zero a1 a2) S)
  | (CCmd.bv_udiv_one a1 a2) => (__eo_push_proven (__eo_prog_bv_udiv_one a1 a2) S)
  | (CCmd.bv_urem_pow2_not_one a1 a2 a3 a4 a5 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_bv_urem_pow2_not_one a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.bv_urem_one a1 a2) => (__eo_push_proven (__eo_prog_bv_urem_one a1 a2) S)
  | (CCmd.bv_urem_self a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_urem_self a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_shl_zero a1 a2) => (__eo_push_proven (__eo_prog_bv_shl_zero a1 a2) S)
  | (CCmd.bv_lshr_zero a1 a2) => (__eo_push_proven (__eo_prog_bv_lshr_zero a1 a2) S)
  | (CCmd.bv_ashr_zero a1 a2) => (__eo_push_proven (__eo_prog_bv_ashr_zero a1 a2) S)
  | (CCmd.bv_ugt_urem a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_bv_ugt_urem a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_ult_one a1 a2 n1) => (__eo_push_proven (__eo_prog_bv_ult_one a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_merge_sign_extend_1 a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_bv_merge_sign_extend_1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.bv_merge_sign_extend_2 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_bv_merge_sign_extend_2 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_sign_extend_eq_const_1 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_sign_extend_eq_const_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_sign_extend_eq_const_2 a1 a2 a3 a4 a5 a6 a7 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_sign_extend_eq_const_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_zero_extend_eq_const_1 a1 a2 a3 a4 a5 a6 n1 n2) => (__eo_push_proven (__eo_prog_bv_zero_extend_eq_const_1 a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_zero_extend_eq_const_2 a1 a2 a3 a4 a5 a6 n1 n2) => (__eo_push_proven (__eo_prog_bv_zero_extend_eq_const_2 a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_zero_extend_ult_const_1 a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_bv_zero_extend_ult_const_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_zero_extend_ult_const_2 a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_bv_zero_extend_ult_const_2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_sign_extend_ult_const_1 a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_bv_sign_extend_ult_const_1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_sign_extend_ult_const_2 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_sign_extend_ult_const_2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.bv_sign_extend_ult_const_3 a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_bv_sign_extend_ult_const_3 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.bv_sign_extend_ult_const_4 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_bv_sign_extend_ult_const_4 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.sets_eq_singleton_emp a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_eq_singleton_emp a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_member_singleton a1 a2) => (__eo_push_proven (__eo_prog_sets_member_singleton a1 a2) S)
  | (CCmd.sets_member_emp a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_member_emp a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_subset_elim a1 a2) => (__eo_push_proven (__eo_prog_sets_subset_elim a1 a2) S)
  | (CCmd.sets_union_comm a1 a2) => (__eo_push_proven (__eo_prog_sets_union_comm a1 a2) S)
  | (CCmd.sets_inter_comm a1 a2) => (__eo_push_proven (__eo_prog_sets_inter_comm a1 a2) S)
  | (CCmd.sets_inter_emp1 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_inter_emp1 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_inter_emp2 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_inter_emp2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_minus_emp1 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_minus_emp1 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_minus_emp2 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_minus_emp2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_union_emp1 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_union_emp1 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_union_emp2 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_sets_union_emp2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.sets_inter_member a1 a2 a3) => (__eo_push_proven (__eo_prog_sets_inter_member a1 a2 a3) S)
  | (CCmd.sets_minus_member a1 a2 a3) => (__eo_push_proven (__eo_prog_sets_minus_member a1 a2 a3) S)
  | (CCmd.sets_union_member a1 a2 a3) => (__eo_push_proven (__eo_prog_sets_union_member a1 a2 a3) S)
  | (CCmd.sets_choose_singleton a1) => (__eo_push_proven (__eo_prog_sets_choose_singleton a1) S)
  | (CCmd.sets_minus_self a1 a2) => (__eo_push_proven (__eo_prog_sets_minus_self a1 a2) S)
  | (CCmd.sets_is_empty_elim a1 a2) => (__eo_push_proven (__eo_prog_sets_is_empty_elim a1 a2) S)
  | (CCmd.sets_is_singleton_elim a1) => (__eo_push_proven (__eo_prog_sets_is_singleton_elim a1) S)
  | (CCmd.str_eq_ctn_false a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_eq_ctn_false a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_ctn_full_false1 a1 a2 n1) => (__eo_push_proven (__eo_prog_str_eq_ctn_full_false1 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_ctn_full_false2 a1 a2 n1) => (__eo_push_proven (__eo_prog_str_eq_ctn_full_false2 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_len_false a1 a2 n1) => (__eo_push_proven (__eo_prog_str_eq_len_false a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_empty_str a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_substr_empty_str a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_empty_range a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_empty_range a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_empty_start a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_empty_start a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_empty_start_neg a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_empty_start_neg a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_substr_start_geq_len a1 a2 a3 a4 a5 a6 n1) => (__eo_push_proven (__eo_prog_str_substr_substr_start_geq_len a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_eq_empty a1 a2 a3 a4 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_eq_empty a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_substr_z_eq_empty_leq a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_substr_z_eq_empty_leq a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_substr_eq_empty_leq_len a1 a2 a3 a4 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_len_replace_inv a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_len_replace_inv a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_len_replace_all_inv a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_len_replace_all_inv a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_len_update_inv a1 a2 a3) => (__eo_push_proven (__eo_prog_str_len_update_inv a1 a2 a3) S)
  | (CCmd.str_update_in_first_concat a1 a2 a3 a4 a5 a6 n1 n2 n3 n4) => (__eo_push_proven (__eo_prog_str_update_in_first_concat a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3)) (Proof.pf (__eo_state_proven_nth S n4))) S)
  | (CCmd.str_len_substr_in_range a1 a2 a3 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_len_substr_in_range a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_concat_clash a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_concat_clash a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_concat_clash_rev a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_concat_clash_rev a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_concat_clash2 a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_concat_clash2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_concat_clash2_rev a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_concat_clash2_rev a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_concat_unify a1 a2 a3 a4 a5) => (__eo_push_proven (__eo_prog_str_concat_unify a1 a2 a3 a4 a5) S)
  | (CCmd.str_concat_unify_rev a1 a2 a3 a4 a5) => (__eo_push_proven (__eo_prog_str_concat_unify_rev a1 a2 a3 a4 a5) S)
  | (CCmd.str_concat_unify_base a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_concat_unify_base a1 a2 a3 a4) S)
  | (CCmd.str_concat_unify_base_rev a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_concat_unify_base_rev a1 a2 a3 a4) S)
  | (CCmd.str_prefixof_elim a1 a2) => (__eo_push_proven (__eo_prog_str_prefixof_elim a1 a2) S)
  | (CCmd.str_suffixof_elim a1 a2) => (__eo_push_proven (__eo_prog_str_suffixof_elim a1 a2) S)
  | (CCmd.str_prefixof_eq a1 a2 n1) => (__eo_push_proven (__eo_prog_str_prefixof_eq a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_suffixof_eq a1 a2 n1) => (__eo_push_proven (__eo_prog_str_suffixof_eq a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_prefixof_one a1 a2 n1) => (__eo_push_proven (__eo_prog_str_prefixof_one a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_suffixof_one a1 a2 n1) => (__eo_push_proven (__eo_prog_str_suffixof_one a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_combine1 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_combine1 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_substr_combine2 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_combine2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_substr_combine3 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_combine3 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_substr_combine4 a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_substr_combine4 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_substr_concat1 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_substr_concat1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_substr_concat2 a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_str_substr_concat2 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_replace a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_substr_replace a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_substr_full a1 a2 n1) => (__eo_push_proven (__eo_prog_str_substr_full a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_full_eq a1 a2 n1) => (__eo_push_proven (__eo_prog_str_substr_full_eq a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_refl a1) => (__eo_push_proven (__eo_prog_str_contains_refl a1) S)
  | (CCmd.str_contains_concat_find a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_contains_concat_find a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_concat_find_contra a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_contains_concat_find_contra a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_split_char a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_contains_split_char a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_leq_len_eq a1 a2 n1) => (__eo_push_proven (__eo_prog_str_contains_leq_len_eq a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_emp a1 a2 n1) => (__eo_push_proven (__eo_prog_str_contains_emp a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_char a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_contains_char a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_at_elim a1 a2) => (__eo_push_proven (__eo_prog_str_at_elim a1 a2) S)
  | (CCmd.str_replace_self a1 a2) => (__eo_push_proven (__eo_prog_str_replace_self a1 a2) S)
  | (CCmd.str_replace_id a1 a2) => (__eo_push_proven (__eo_prog_str_replace_id a1 a2) S)
  | (CCmd.str_replace_prefix a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_replace_prefix a1 a2 a3 a4) S)
  | (CCmd.str_replace_no_contains a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_replace_no_contains a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_find_base a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_replace_find_base a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_replace_find_first_concat a1 a2 a3 a4 a5 a6 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_replace_find_first_concat a1 a2 a3 a4 a5 a6 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_replace_empty a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_replace_empty a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_one_pre a1 a2 a3 a4 a5 n1) => (__eo_push_proven (__eo_prog_str_replace_one_pre a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_find_pre a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_replace_find_pre a1 a2 a3 a4) S)
  | (CCmd.str_replace_all_no_contains a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_replace_all_no_contains a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_all_empty a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_replace_all_empty a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_all_id a1 a2) => (__eo_push_proven (__eo_prog_str_replace_all_id a1 a2) S)
  | (CCmd.str_replace_all_self a1 a2 n1) => (__eo_push_proven (__eo_prog_str_replace_all_self a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_replace_re_none a1 a2) => (__eo_push_proven (__eo_prog_str_replace_re_none a1 a2) S)
  | (CCmd.str_replace_re_all_none a1 a2) => (__eo_push_proven (__eo_prog_str_replace_re_all_none a1 a2) S)
  | (CCmd.str_len_concat_rec a1 a2 a3) => (__eo_push_proven (__eo_prog_str_len_concat_rec a1 a2 a3) S)
  | (CCmd.str_len_eq_zero_concat_rec a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_len_eq_zero_concat_rec a1 a2 a3 a4) S)
  | (CCmd.str_len_eq_zero_base a1 a2) => (__eo_push_proven (__eo_prog_str_len_eq_zero_base a1 a2) S)
  | (CCmd.str_indexof_self a1 a2 a3) => (__eo_push_proven (__eo_prog_str_indexof_self a1 a2 a3) S)
  | (CCmd.str_indexof_no_contains a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_indexof_no_contains a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_indexof_oob a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_indexof_oob a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_indexof_oob2 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_indexof_oob2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_indexof_contains_pre a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_indexof_contains_pre a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_indexof_contains_concat_pre a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_indexof_contains_concat_pre a1 a2 a3 a4) S)
  | (CCmd.str_indexof_find_emp a1 a2 a3 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_indexof_find_emp a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_indexof_eq_irr a1 a2 a3 a4 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_indexof_eq_irr a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_indexof_re_none a1 a2) => (__eo_push_proven (__eo_prog_str_indexof_re_none a1 a2) S)
  | (CCmd.str_indexof_re_emp_re a1 a2 a3 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_indexof_re_emp_re a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_to_lower_concat a1 a2 a3) => (__eo_push_proven (__eo_prog_str_to_lower_concat a1 a2 a3) S)
  | (CCmd.str_to_upper_concat a1 a2 a3) => (__eo_push_proven (__eo_prog_str_to_upper_concat a1 a2 a3) S)
  | (CCmd.str_to_lower_upper a1) => (__eo_push_proven (__eo_prog_str_to_lower_upper a1) S)
  | (CCmd.str_to_upper_lower a1) => (__eo_push_proven (__eo_prog_str_to_upper_lower a1) S)
  | (CCmd.str_to_lower_len a1) => (__eo_push_proven (__eo_prog_str_to_lower_len a1) S)
  | (CCmd.str_to_upper_len a1) => (__eo_push_proven (__eo_prog_str_to_upper_len a1) S)
  | (CCmd.str_to_lower_from_int a1) => (__eo_push_proven (__eo_prog_str_to_lower_from_int a1) S)
  | (CCmd.str_to_upper_from_int a1) => (__eo_push_proven (__eo_prog_str_to_upper_from_int a1) S)
  | (CCmd.str_to_int_concat_neg_one a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_to_int_concat_neg_one a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_is_digit_elim a1) => (__eo_push_proven (__eo_prog_str_is_digit_elim a1) S)
  | (CCmd.str_leq_empty a1) => (__eo_push_proven (__eo_prog_str_leq_empty a1) S)
  | (CCmd.str_leq_empty_eq a1) => (__eo_push_proven (__eo_prog_str_leq_empty_eq a1) S)
  | (CCmd.str_leq_concat_false a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_str_leq_concat_false a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_leq_concat_true a1 a2 a3 a4 a5 n1 n2 n3) => (__eo_push_proven (__eo_prog_str_leq_concat_true a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.str_leq_concat_base_1 a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_leq_concat_base_1 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_leq_concat_base_2 a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_leq_concat_base_2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_lt_elim a1 a2) => (__eo_push_proven (__eo_prog_str_lt_elim a1 a2) S)
  | (CCmd.str_from_int_no_ctn_nondigit a1 a2 n1 n2) => (__eo_push_proven (__eo_prog_str_from_int_no_ctn_nondigit a1 a2 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_substr_ctn_contra a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_ctn_contra a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_ctn a1 a2 a3) => (__eo_push_proven (__eo_prog_str_substr_ctn a1 a2 a3) S)
  | (CCmd.str_replace_dual_ctn a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_replace_dual_ctn a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_replace_dual_ctn_false a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_replace_dual_ctn_false a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_replace_self_ctn_simp a1 a2) => (__eo_push_proven (__eo_prog_str_replace_self_ctn_simp a1 a2) S)
  | (CCmd.str_replace_emp_ctn_src a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_replace_emp_ctn_src a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_char_start_eq_len a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_substr_char_start_eq_len a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_repl_char a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_contains_repl_char a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_contains_repl_self_tgt_char a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_contains_repl_self_tgt_char a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_contains_repl_self a1 a2) => (__eo_push_proven (__eo_prog_str_contains_repl_self a1 a2) S)
  | (CCmd.str_contains_repl_tgt a1 a2 a3) => (__eo_push_proven (__eo_prog_str_contains_repl_tgt a1 a2 a3) S)
  | (CCmd.str_repl_repl_len_id a1 a2 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_len_id a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_src_tgt_no_ctn a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_src_tgt_no_ctn a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_tgt_self a1 a2) => (__eo_push_proven (__eo_prog_str_repl_repl_tgt_self a1 a2) S)
  | (CCmd.str_repl_repl_tgt_no_ctn a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_tgt_no_ctn a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_src_self a1 a2 a3) => (__eo_push_proven (__eo_prog_str_repl_repl_src_self a1 a2 a3) S)
  | (CCmd.str_repl_repl_src_inv_no_ctn1 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_src_inv_no_ctn1 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_src_inv_no_ctn2 a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_src_inv_no_ctn2 a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_src_inv_no_ctn3 a1 a2 a3 a4 a5 n1 n2) => (__eo_push_proven (__eo_prog_str_repl_repl_src_inv_no_ctn3 a1 a2 a3 a4 a5 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_repl_repl_dual_self a1 a2) => (__eo_push_proven (__eo_prog_str_repl_repl_dual_self a1 a2) S)
  | (CCmd.str_repl_repl_dual_ite1 a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_repl_repl_dual_ite1 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_repl_repl_dual_ite2 a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_repl_repl_dual_ite2 a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_repl_repl_lookahead_id_simp a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_repl_repl_lookahead_id_simp a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | CCmd.re_all_elim => (__eo_push_proven (Term.Apply (Term.Apply Term.eq Term.re_all) (Term.Apply Term.re_mult Term.re_allchar)) S)
  | (CCmd.re_opt_elim a1) => (__eo_push_proven (__eo_prog_re_opt_elim a1) S)
  | (CCmd.re_diff_elim a1 a2) => (__eo_push_proven (__eo_prog_re_diff_elim a1 a2) S)
  | (CCmd.re_plus_elim a1) => (__eo_push_proven (__eo_prog_re_plus_elim a1) S)
  | (CCmd.re_repeat_elim a1 a2) => (__eo_push_proven (__eo_prog_re_repeat_elim a1 a2) S)
  | (CCmd.re_concat_star_swap a1 a2 a3) => (__eo_push_proven (__eo_prog_re_concat_star_swap a1 a2 a3) S)
  | (CCmd.re_concat_star_repeat a1 a2 a3) => (__eo_push_proven (__eo_prog_re_concat_star_repeat a1 a2 a3) S)
  | (CCmd.re_concat_star_subsume1 a1 a2 a3) => (__eo_push_proven (__eo_prog_re_concat_star_subsume1 a1 a2 a3) S)
  | (CCmd.re_concat_star_subsume2 a1 a2 a3) => (__eo_push_proven (__eo_prog_re_concat_star_subsume2 a1 a2 a3) S)
  | (CCmd.re_concat_merge a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_re_concat_merge a1 a2 a3 a4) S)
  | (CCmd.re_union_all a1 a2) => (__eo_push_proven (__eo_prog_re_union_all a1 a2) S)
  | (CCmd.re_union_const_elim a1 a2 n1) => (__eo_push_proven (__eo_prog_re_union_const_elim a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_inter_all a1 a2) => (__eo_push_proven (__eo_prog_re_inter_all a1 a2) S)
  | CCmd.re_star_none => (__eo_push_proven (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult Term.re_none)) (Term.Apply Term.str_to_re (Term.String ""))) S)
  | CCmd.re_star_emp => (__eo_push_proven (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String "")))) (Term.Apply Term.str_to_re (Term.String ""))) S)
  | (CCmd.re_star_star a1) => (__eo_push_proven (__eo_prog_re_star_star a1) S)
  | (CCmd.re_range_refl a1 n1) => (__eo_push_proven (__eo_prog_re_range_refl a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_range_emp a1 a2 n1 n2 n3) => (__eo_push_proven (__eo_prog_re_range_emp a1 a2 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)) (Proof.pf (__eo_state_proven_nth S n3))) S)
  | (CCmd.re_range_non_singleton_1 a1 a2 n1) => (__eo_push_proven (__eo_prog_re_range_non_singleton_1 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_range_non_singleton_2 a1 a2 n1) => (__eo_push_proven (__eo_prog_re_range_non_singleton_2 a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_star_union_char a1 a2) => (__eo_push_proven (__eo_prog_re_star_union_char a1 a2) S)
  | (CCmd.re_star_union_drop_emp a1 a2) => (__eo_push_proven (__eo_prog_re_star_union_drop_emp a1 a2) S)
  | (CCmd.re_loop_neg a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_re_loop_neg a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_inter_cstring a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_re_inter_cstring a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.re_inter_cstring_neg a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_re_inter_cstring_neg a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_len_include a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_len_include a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_len_include_pre a1 a2 a3 a4 n1) => (__eo_push_proven (__eo_prog_str_substr_len_include_pre a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_substr_len_norm a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_substr_len_norm a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.seq_len_rev a1) => (__eo_push_proven (__eo_prog_seq_len_rev a1) S)
  | (CCmd.seq_rev_rev a1) => (__eo_push_proven (__eo_prog_seq_rev_rev a1) S)
  | (CCmd.seq_rev_concat a1 a2 a3) => (__eo_push_proven (__eo_prog_seq_rev_concat a1 a2 a3) S)
  | (CCmd.str_eq_repl_self_emp a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_eq_repl_self_emp a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_repl_no_change a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_eq_repl_no_change a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_repl_tgt_eq_len a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_str_eq_repl_tgt_eq_len a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_eq_repl_len_one_emp_prefix a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_eq_repl_len_one_emp_prefix a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_eq_repl_emp_tgt_nemp a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_eq_repl_emp_tgt_nemp a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_eq_repl_nemp_src_emp a1 a2 a3 a4 n1 n2) => (__eo_push_proven (__eo_prog_str_eq_repl_nemp_src_emp a1 a2 a3 a4 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_eq_repl_self_src a1 a2) => (__eo_push_proven (__eo_prog_str_eq_repl_self_src a1 a2) S)
  | (CCmd.seq_len_unit a1) => (__eo_push_proven (__eo_prog_seq_len_unit a1) S)
  | (CCmd.seq_nth_unit a1) => (__eo_push_proven (__eo_prog_seq_nth_unit a1) S)
  | (CCmd.seq_rev_unit a1) => (__eo_push_proven (__eo_prog_seq_rev_unit a1) S)
  | (CCmd.re_in_empty a1) => (__eo_push_proven (__eo_prog_re_in_empty a1) S)
  | (CCmd.re_in_sigma a1) => (__eo_push_proven (__eo_prog_re_in_sigma a1) S)
  | (CCmd.re_in_sigma_star a1) => (__eo_push_proven (__eo_prog_re_in_sigma_star a1) S)
  | (CCmd.re_in_cstring a1 a2) => (__eo_push_proven (__eo_prog_re_in_cstring a1 a2) S)
  | (CCmd.re_in_comp a1 a2) => (__eo_push_proven (__eo_prog_re_in_comp a1 a2) S)
  | (CCmd.str_in_re_union_elim a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_in_re_union_elim a1 a2 a3 a4) S)
  | (CCmd.str_in_re_inter_elim a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_str_in_re_inter_elim a1 a2 a3 a4) S)
  | (CCmd.str_in_re_range_elim a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_str_in_re_range_elim a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.str_in_re_contains a1 a2) => (__eo_push_proven (__eo_prog_str_in_re_contains a1 a2) S)
  | (CCmd.str_in_re_from_int_nemp_dig_range a1 n1) => (__eo_push_proven (__eo_prog_str_in_re_from_int_nemp_dig_range a1 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.str_in_re_from_int_dig_range a1) => (__eo_push_proven (__eo_prog_str_in_re_from_int_dig_range a1) S)
  | (CCmd.eq_refl a1) => (__eo_push_proven (__eo_prog_eq_refl a1) S)
  | (CCmd.eq_symm a1 a2) => (__eo_push_proven (__eo_prog_eq_symm a1 a2) S)
  | (CCmd.eq_cond_deq a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_eq_cond_deq a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.eq_ite_lift a1 a2 a3 a4) => (__eo_push_proven (__eo_prog_eq_ite_lift a1 a2 a3 a4) S)
  | (CCmd.distinct_binary_elim a1 a2) => (__eo_push_proven (__eo_prog_distinct_binary_elim a1 a2) S)
  | (CCmd.uf_bv2nat_int2bv a1 a2 n1) => (__eo_push_proven (__eo_prog_uf_bv2nat_int2bv a1 a2 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.uf_bv2nat_int2bv_extend a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.uf_bv2nat_int2bv_extract a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.uf_int2bv_bv2nat a1 a2) => (__eo_push_proven (__eo_prog_uf_int2bv_bv2nat a1 a2) S)
  | (CCmd.uf_bv2nat_geq_elim a1 a2 a3 n1) => (__eo_push_proven (__eo_prog_uf_bv2nat_geq_elim a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1))) S)
  | (CCmd.uf_int2bv_bvult_equiv a1 a2) => (__eo_push_proven (__eo_prog_uf_int2bv_bvult_equiv a1 a2) S)
  | (CCmd.uf_int2bv_bvule_equiv a1 a2) => (__eo_push_proven (__eo_prog_uf_int2bv_bvule_equiv a1 a2) S)
  | (CCmd.uf_sbv_to_int_elim a1 a2 a3 n1 n2) => (__eo_push_proven (__eo_prog_uf_sbv_to_int_elim a1 a2 a3 (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2))) S)
  | (CCmd.evaluate a1) => (__eo_push_proven (__eo_prog_evaluate a1) S)
  | (CCmd.distinct_values a1 a2) => (__eo_push_proven (__eo_prog_distinct_values a1 a2) S)
  | (CCmd.aci_norm a1) => (__eo_push_proven (__eo_prog_aci_norm a1) S)
  | (CCmd.absorb a1) => (__eo_push_proven (__eo_prog_absorb a1) S)
  | (CCmd.distinct_card_conflict a1) => (__eo_push_proven (__eo_prog_distinct_card_conflict a1) S)


def __eo_invoke_cmd_list : CState -> CCmdList -> CState
  | CState.Stuck, cmds => CState.Stuck
  | S, CCmdList.nil => S
  | S, (CCmdList.cons c cmds) => (__eo_invoke_cmd_list (__eo_invoke_cmd S c) cmds)


def __eo_invoke_cmd_list_assuming (S : CState) : Term -> CCmdList -> CState
  | (Term.Apply (Term.Apply Term.and F) as), cs => (__eo_invoke_cmd_list_assuming (CState.cons (CStateObj.assume F) S) as cs)
  | (Term.Boolean true), cs => (__eo_invoke_cmd_list S cs)
  | as, cs => CState.Stuck


def __eo_checker_is_refutation : Term -> CCmdList -> Term
  | Term.Stuck , _  => Term.Stuck
  | as, cs => (__eo_state_is_closed (__eo_invoke_cmd_check_proven (__eo_invoke_cmd_list_assuming CState.nil as cs) (Term.Boolean false)))





end Eo
