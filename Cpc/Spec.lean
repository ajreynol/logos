import Cpc.SmtModel
import Cpc.Logos

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- Definitions for theorems -/

/- Definition of refutation -/

inductive eo_is_refutation : Term -> CCmdList -> Prop
  | intro (F : Term) (c : CCmdList) : 
    (__eo_checker_is_refutation F c) = true -> (eo_is_refutation F c)


/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev ObjectTerm := SmtTerm

abbrev ObjectModel := SmtModel

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
abbrev obj_interprets := smt_interprets

/-
Definitions for eo_is_obj
-/
noncomputable section

mutual

def __eo_to_smt_is_var (s1 : native_String) (T1 : SmtType) : SmtTerm -> native_Bool
  | (SmtTerm.Var s2 T2) => (native_and (native_streq s1 s2) (native_Teq T1 T2))
  | x => false


def __eo_to_smt_substitute (s : native_String) (T : SmtType) (u : SmtTerm) : SmtTerm -> SmtTerm
  | (SmtTerm.Apply f a) => (SmtTerm.Apply (__eo_to_smt_substitute s T u f) (__eo_to_smt_substitute s T u a))
  | z => (native_ite (__eo_to_smt_is_var s T z) u z)


def __eo_to_smt_distinct_pairs (s : SmtTerm) : Term -> SmtTerm
  | (Term.Apply (Term.Apply Term._at__at_TypedList_cons x) xs) => (SmtTerm.and (SmtTerm.not (SmtTerm.eq s (__eo_to_smt x))) (__eo_to_smt_distinct_pairs s xs))
  | (Term.Apply Term._at__at_TypedList_nil T) => (SmtTerm.Boolean true)
  | xs => SmtTerm.None


def __eo_to_smt_distinct : Term -> SmtTerm
  | (Term.Apply (Term.Apply Term._at__at_TypedList_cons x) xs) => (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt x) xs) (__eo_to_smt_distinct xs))
  | (Term.Apply Term._at__at_TypedList_nil T) => (SmtTerm.Boolean true)
  | xs => SmtTerm.None


def __eo_to_smt__at_bv : SmtTerm -> SmtTerm -> SmtTerm
  | (SmtTerm.Numeral x1), (SmtTerm.Numeral x2) => (native_ite (native_zleq 0 x2) (SmtTerm.Binary x2 (native_mod_total x1 (native_int_pow2 x2))) SmtTerm.None)
  | t1, t2 => SmtTerm.None


def __eo_to_smt_seq_empty : SmtType -> SmtTerm
  | (SmtType.Seq T) => (SmtTerm.seq_empty T)
  | T => SmtTerm.None


def __eo_to_smt_re_unfold_pos_component (s : SmtTerm) : SmtTerm -> native_Nat -> SmtTerm
  | (SmtTerm.re_concat r1 r2), native_nat_zero => 
    let _v0 := (SmtType.Seq SmtType.Char)
    let _v2 := (SmtTerm.Var "_at_x" _v0)
    let _v3 := (SmtTerm.str_len _v2)
    let _v4 := (SmtTerm.str_substr s _v3 (SmtTerm.neg (SmtTerm.str_len s) _v3))
    (SmtTerm.choice "_at_x" _v0 (SmtTerm.and (SmtTerm.eq s (SmtTerm.str_concat _v2 _v4)) (SmtTerm.and (SmtTerm.str_in_re _v2 r1) (SmtTerm.str_in_re _v4 r2))))
  | (SmtTerm.re_concat r1 r2), (native_nat_succ n) => 
    let _v0 := (SmtTerm.str_len (__eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2) native_nat_zero))
    (__eo_to_smt_re_unfold_pos_component (SmtTerm.str_substr s _v0 (SmtTerm.neg (SmtTerm.str_len s) _v0)) r2 n)
  | r1, n => SmtTerm.None


def __eo_to_smt_set_empty : SmtType -> SmtTerm
  | (SmtType.Set T) => (SmtTerm.set_empty T)
  | T => SmtTerm.None


def __eo_to_smt_quantifiers_skolemize : SmtTerm -> native_Nat -> SmtTerm
  | (SmtTerm.exists s T F), n => (SmtTerm.choice_nth s T F n)
  | _, _ => SmtTerm.None


def __eo_to_smt_type_tuple (U : SmtType) : SmtType -> SmtType
  | (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum c SmtDatatype.null)) => (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum (SmtDatatypeCons.cons U c) SmtDatatype.null))
  | T => SmtType.None


def __eo_to_smt_nat : Term -> native_Nat
  | (Term.Numeral n) => (native_int_to_nat n)
  | t => native_nat_zero


def __eo_to_smt_datatype_cons : DatatypeCons -> SmtDatatypeCons
  | DatatypeCons.unit => SmtDatatypeCons.unit
  | (DatatypeCons.cons U c) => (SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c))


def __eo_to_smt_datatype : Datatype -> SmtDatatype
  | (Datatype.sum c d) => (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
  | Datatype.null => SmtDatatype.null


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | (Term.DatatypeType s d) => (SmtType.Datatype s (__eo_to_smt_datatype d))
  | (Term.DatatypeTypeRef s) => (SmtType.TypeRef s)
  | (Term.DtcAppType T1 T2) => 
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.DtcAppType _v1 _v0)))
  | (Term.USort i) => (SmtType.USort i)
  | (Term.Apply (Term.Apply Term.FunType T1) T2) => 
    let _v0 := (__eo_to_smt_type T2)
    let _v1 := (__eo_to_smt_type T1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.FunType _v1 _v0)))
  | Term.Int => SmtType.Int
  | Term.Real => SmtType.Real
  | (Term.Apply Term.BitVec (Term.Numeral n1)) => (native_ite (native_zleq 0 n1) (SmtType.BitVec (native_int_to_nat n1)) SmtType.None)
  | Term.Char => SmtType.Char
  | (Term.Apply Term.Seq x1) => 
    let _v0 := (__eo_to_smt_type x1)
    (__smtx_typeof_guard _v0 (SmtType.Seq _v0))
  | (Term.Apply (Term.Apply Term.Array x1) x2) => 
    let _v0 := (__eo_to_smt_type x2)
    let _v1 := (__eo_to_smt_type x1)
    (__smtx_typeof_guard _v1 (__smtx_typeof_guard _v0 (SmtType.Map _v1 _v0)))
  | Term.RegLan => SmtType.RegLan
  | Term.UnitTuple => (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
  | (Term.Apply (Term.Apply Term.Tuple x1) x2) => (__eo_to_smt_type_tuple (__eo_to_smt_type x1) (__eo_to_smt_type x2))
  | (Term.Apply Term.Set x1) => 
    let _v0 := (__eo_to_smt_type x1)
    (__smtx_typeof_guard _v0 (SmtType.Set _v0))
  | T => SmtType.None


def __eo_to_smt_tuple_app_extend : SmtTerm -> SmtType -> SmtTerm
  | (SmtTerm.Apply f a), T => (SmtTerm.Apply (__eo_to_smt_tuple_app_extend f T) a)
  | (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum c SmtDatatype.null) native_nat_zero), T => (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum (__smtx_dtc_concat c (SmtDatatypeCons.cons T SmtDatatypeCons.unit)) SmtDatatype.null) native_nat_zero)
  | s, T => SmtTerm.None


def __eo_to_smt_tuple_select : SmtType -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtType.Datatype "_at_Tuple" d), (SmtTerm.Numeral n), t => (native_ite (native_zleq 0 n) (SmtTerm.Apply (SmtTerm.DtSel "_at_Tuple" d native_nat_zero (native_int_to_nat n)) t) SmtTerm.None)
  | T, n, t => SmtTerm.None


def __eo_to_smt_tester : SmtTerm -> SmtTerm
  | (SmtTerm.DtCons s d n) => (SmtTerm.DtTester s d n)
  | t => SmtTerm.None


def __eo_to_smt_updater_rec : SmtTerm -> native_Nat -> SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtTerm.DtSel s d n m), native_nat_zero, t, u, acc => acc
  | (SmtTerm.DtSel s d n m), (native_nat_succ k), t, u, acc => 
    let _v0 := (SmtTerm.DtSel s d n m)
    (__eo_to_smt_updater_rec _v0 k t u (SmtTerm.Apply acc (native_ite (native_nateq m k) u (SmtTerm.Apply _v0 t))))
  | v, k, t, u, acc => SmtTerm.None


def __eo_to_smt_updater : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtTerm.DtSel s d n m), t, u => (SmtTerm.ite (SmtTerm.Apply (SmtTerm.DtTester s d n) t) (__eo_to_smt_updater_rec (SmtTerm.DtSel s d n m) (__smtx_dt_num_sels d n) t u (SmtTerm.DtCons s d n)) t)
  | sel, t, d => SmtTerm.None


def __eo_to_smt_tuple_update : SmtType -> SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtType.Datatype "_at_Tuple" d), (SmtTerm.Numeral n), t, u => (native_ite (native_zleq 0 n) (__eo_to_smt_updater (SmtTerm.DtSel "_at_Tuple" d native_nat_zero (native_int_to_nat n)) t u) SmtTerm.None)
  | T, n, t, u => SmtTerm.None


def __eo_to_smt_exists : Term -> SmtTerm -> SmtTerm
  | Term.__eo_List_nil, F => F
  | (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs), F => (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists vs F))
  | vs, F => SmtTerm.None


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var (Term.String s) T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | (Term.DtCons s d i) => (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
  | (Term.DtSel s d i j) => (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j)
  | (Term.UConst i T) => (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
  | (Term.Apply (Term.Apply (Term.Apply Term.ite x1) x2) x3) => (SmtTerm.ite (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply Term.not x1) => (SmtTerm.not (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.or x1) x2) => (SmtTerm.or (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.and x1) x2) => (SmtTerm.and (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.imp x1) x2) => (SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.xor x1) x2) => (SmtTerm.xor (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.eq x1) x2) => (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.distinct x1) => (__eo_to_smt_distinct x1)
  | (Term._at_purify x1) => (__eo_to_smt x1)
  | (Term.Apply (Term.Apply Term.plus x1) x2) => (SmtTerm.plus (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.neg x1) x2) => (SmtTerm.neg (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mult x1) x2) => (SmtTerm.mult (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.lt x1) x2) => (SmtTerm.lt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.leq x1) x2) => (SmtTerm.leq (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.gt x1) x2) => (SmtTerm.gt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.geq x1) x2) => (SmtTerm.geq (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.to_real x1) => (SmtTerm.to_real (__eo_to_smt x1))
  | (Term.Apply Term.to_int x1) => (SmtTerm.to_int (__eo_to_smt x1))
  | (Term.Apply Term.is_int x1) => (SmtTerm.is_int (__eo_to_smt x1))
  | (Term.Apply Term.abs x1) => (SmtTerm.abs (__eo_to_smt x1))
  | (Term.Apply Term.__eoo_neg_2 x1) => (SmtTerm.uneg (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.div x1) x2) => (SmtTerm.div (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mod x1) x2) => (SmtTerm.mod (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.multmult x1) x2) => (SmtTerm.multmult (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.divisible x1) x2) => (SmtTerm.divisible (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.int_pow2 x1) => (SmtTerm.int_pow2 (__eo_to_smt x1))
  | (Term.Apply Term.int_log2 x1) => (SmtTerm.int_log2 (__eo_to_smt x1))
  | (Term.Apply Term.int_ispow2 x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.and (SmtTerm.geq _v0 (SmtTerm.Numeral 0)) (SmtTerm.eq _v0 (SmtTerm.int_pow2 (SmtTerm.int_log2 _v0))))
  | (Term.Apply (Term.Apply Term.div_total x1) x2) => (SmtTerm.div_total (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mod_total x1) x2) => (SmtTerm.mod_total (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.multmult_total x1) x2) => (SmtTerm.multmult_total (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term._at_int_div_by_zero x1) => (SmtTerm.div (__eo_to_smt x1) (SmtTerm.Numeral 0))
  | (Term.Apply Term._at_mod_by_zero x1) => (SmtTerm.mod (__eo_to_smt x1) (SmtTerm.Numeral 0))
  | (Term.Apply (Term.Apply Term.select x1) x2) => (SmtTerm.select (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.store x1) x2) x3) => (SmtTerm.store (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term._at_array_deq_diff x1 x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
    let _v2 := (SmtTerm.Var "_at_x" _v0)
    (SmtTerm.choice "_at_x" _v0 (SmtTerm.not (SmtTerm.eq (SmtTerm.select (__eo_to_smt x1) _v2) (SmtTerm.select (__eo_to_smt x2) _v2))))
  | (Term.Apply Term._at_bvsize x1) => (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x1))))
  | (Term.Apply (Term.Apply Term.concat x1) x2) => (SmtTerm.concat (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.extract x1) x2) x3) => (SmtTerm.extract (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.repeat x1) x2) => (SmtTerm.repeat (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.bvnot x1) => (SmtTerm.bvnot (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvand x1) x2) => (SmtTerm.bvand (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvor x1) x2) => (SmtTerm.bvor (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvnand x1) x2) => (SmtTerm.bvnand (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvnor x1) x2) => (SmtTerm.bvnor (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvxor x1) x2) => (SmtTerm.bvxor (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvxnor x1) x2) => (SmtTerm.bvxnor (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvcomp x1) x2) => (SmtTerm.bvcomp (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.bvneg x1) => (SmtTerm.bvneg (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvadd x1) x2) => (SmtTerm.bvadd (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvmul x1) x2) => (SmtTerm.bvmul (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvudiv x1) x2) => (SmtTerm.bvudiv (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvurem x1) x2) => (SmtTerm.bvurem (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsub x1) x2) => (SmtTerm.bvsub (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsdiv x1) x2) => (SmtTerm.bvsdiv (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsrem x1) x2) => (SmtTerm.bvsrem (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsmod x1) x2) => (SmtTerm.bvsmod (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvult x1) x2) => (SmtTerm.bvult (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvule x1) x2) => (SmtTerm.bvule (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvugt x1) x2) => (SmtTerm.bvugt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvuge x1) x2) => (SmtTerm.bvuge (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvslt x1) x2) => (SmtTerm.bvslt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsle x1) x2) => (SmtTerm.bvsle (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsgt x1) x2) => (SmtTerm.bvsgt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsge x1) x2) => (SmtTerm.bvsge (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvshl x1) x2) => (SmtTerm.bvshl (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvlshr x1) x2) => (SmtTerm.bvlshr (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvashr x1) x2) => (SmtTerm.bvashr (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.zero_extend x1) x2) => (SmtTerm.zero_extend (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.sign_extend x1) x2) => (SmtTerm.sign_extend (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.rotate_left x1) x2) => (SmtTerm.rotate_left (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.rotate_right x1) x2) => (SmtTerm.rotate_right (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.bvite x1) x2) x3) => (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x1) (SmtTerm.Binary 1 1)) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.bvuaddo x1) x2) => (SmtTerm.bvuaddo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.bvnego x1) => (SmtTerm.bvnego (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvsaddo x1) x2) => (SmtTerm.bvsaddo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvumulo x1) x2) => (SmtTerm.bvumulo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsmulo x1) x2) => (SmtTerm.bvsmulo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvusubo x1) x2) => (SmtTerm.bvusubo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvssubo x1) x2) => (SmtTerm.bvssubo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsdivo x1) x2) => (SmtTerm.bvsdivo (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvultbv x1) x2) => (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt x1) (__eo_to_smt x2)) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
  | (Term.Apply (Term.Apply Term.bvsltbv x1) x2) => (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt x1) (__eo_to_smt x2)) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
  | (Term.Apply Term.bvredand x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.bvcomp _v0 (SmtTerm.bvnot (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)))
  | (Term.Apply Term.bvredor x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.bvnot (SmtTerm.bvcomp _v0 (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)))
  | (Term.Apply (Term.Apply Term._at_bit x1) x2) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.extract _v0 _v0 (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term._at_from_bools x1) x2) => (SmtTerm.concat (SmtTerm.ite (__eo_to_smt x1) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term._at_bv x1) x2) => (__eo_to_smt__at_bv (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.seq_empty x1) => (__eo_to_smt_seq_empty (__eo_to_smt_type x1))
  | (Term.Apply Term.str_len x1) => (SmtTerm.str_len (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.str_concat x1) x2) => (SmtTerm.str_concat (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) x2) x3) => (SmtTerm.str_substr (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_contains x1) x2) => (SmtTerm.str_contains (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) x2) x3) => (SmtTerm.str_replace (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x1) x2) x3) => (SmtTerm.str_indexof (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_at x1) x2) => (SmtTerm.str_at (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_prefixof x1) x2) => (SmtTerm.str_prefixof (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_suffixof x1) x2) => (SmtTerm.str_suffixof (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.str_rev x1) => (SmtTerm.str_rev (__eo_to_smt x1))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_update x1) x2) x3) => (SmtTerm.str_update (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply Term.str_to_lower x1) => (SmtTerm.str_to_lower (__eo_to_smt x1))
  | (Term.Apply Term.str_to_upper x1) => (SmtTerm.str_to_upper (__eo_to_smt x1))
  | (Term.Apply Term.str_to_code x1) => (SmtTerm.str_to_code (__eo_to_smt x1))
  | (Term.Apply Term.str_from_code x1) => (SmtTerm.str_from_code (__eo_to_smt x1))
  | (Term.Apply Term.str_is_digit x1) => (SmtTerm.str_is_digit (__eo_to_smt x1))
  | (Term.Apply Term.str_to_int x1) => (SmtTerm.str_to_int (__eo_to_smt x1))
  | (Term.Apply Term.str_from_int x1) => (SmtTerm.str_from_int (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.str_lt x1) x2) => (SmtTerm.str_lt (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_leq x1) x2) => (SmtTerm.str_leq (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x1) x2) x3) => (SmtTerm.str_replace_all (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re x1) x2) x3) => (SmtTerm.str_replace_re (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all x1) x2) x3) => (SmtTerm.str_replace_re_all (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re x1) x2) x3) => (SmtTerm.str_indexof_re (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | Term.re_allchar => SmtTerm.re_allchar
  | Term.re_none => SmtTerm.re_none
  | Term.re_all => SmtTerm.re_all
  | (Term.Apply Term.str_to_re x1) => (SmtTerm.str_to_re (__eo_to_smt x1))
  | (Term.Apply Term.re_mult x1) => (SmtTerm.re_mult (__eo_to_smt x1))
  | (Term.Apply Term.re_plus x1) => (SmtTerm.re_plus (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.re_exp x1) x2) => (SmtTerm.re_exp (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.re_opt x1) => (SmtTerm.re_opt (__eo_to_smt x1))
  | (Term.Apply Term.re_comp x1) => (SmtTerm.re_comp (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.re_range x1) x2) => (SmtTerm.re_range (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_concat x1) x2) => (SmtTerm.re_concat (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_inter x1) x2) => (SmtTerm.re_inter (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_union x1) x2) => (SmtTerm.re_union (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_diff x1) x2) => (SmtTerm.re_diff (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.re_loop x1) x2) x3) => (SmtTerm.re_loop (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_in_re x1) x2) => (SmtTerm.str_in_re (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.seq_unit x1) => (SmtTerm.seq_unit (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.seq_nth x1) x2) => (SmtTerm.seq_nth (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term._at_re_unfold_pos_component x1) x2) x3) => (native_ite (native_teq (__eo_is_neg x3) (Term.Boolean false)) (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt_nat x3)) SmtTerm.None)
  | (Term.Apply (Term.Apply Term._at_strings_deq_diff x1) x2) => 
    let _v0 := (SmtTerm.Numeral 1)
    let _v2 := (SmtTerm.Var "_at_x" SmtType.Int)
    (SmtTerm.choice "_at_x" SmtType.Int (SmtTerm.not (SmtTerm.eq (SmtTerm.str_substr (__eo_to_smt x1) _v2 _v0) (SmtTerm.str_substr (__eo_to_smt x2) _v2 _v0))))
  | (Term.Apply (Term.Apply Term._at_strings_stoi_result x1) x2) => (SmtTerm.str_to_int (SmtTerm.str_substr (__eo_to_smt x1) (SmtTerm.Numeral 0) (__eo_to_smt x2)))
  | (Term.Apply Term._at_strings_stoi_non_digit x1) => (SmtTerm.str_indexof_re (__eo_to_smt x1) (SmtTerm.re_comp (SmtTerm.re_range (SmtTerm.String "0") (SmtTerm.String "9"))) (SmtTerm.Numeral 0))
  | (Term.Apply (Term.Apply Term._at_strings_itos_result x1) x2) => (SmtTerm.str_from_int (SmtTerm.mod (__eo_to_smt x1) (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x2))))
  | (Term.Apply (Term.Apply Term._at_strings_num_occur x1) x2) => 
    let _v0 := (__eo_to_smt x2)
    let _v1 := (__eo_to_smt x1)
    (SmtTerm.div (SmtTerm.neg (SmtTerm.str_len _v1) (SmtTerm.str_len (SmtTerm.str_replace_all _v1 _v0 (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))))) (SmtTerm.str_len _v0))
  | (Term.Apply (Term.Apply (Term.Apply Term._at_witness_string_length x1) x2) x3) => 
    let _v0 := (__eo_to_smt_type x1)
    (SmtTerm.choice "_at_x" _v0 (SmtTerm.eq (SmtTerm.str_len (SmtTerm.Var "_at_x" _v0)) (__eo_to_smt x2)))
  | (Term.Apply Term.is x1) => (__eo_to_smt_tester (__eo_to_smt x1))
  | (Term.Apply (Term.Apply (Term.Apply Term.update x1) x2) x3) => (__eo_to_smt_updater (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | Term.tuple_unit => (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) native_nat_zero)
  | (Term.Apply (Term.Apply Term.tuple x1) x2) => (SmtTerm.Apply (__eo_to_smt_tuple_app_extend (__eo_to_smt x1) (__eo_to_smt_type (__eo_typeof x2))) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.tuple_select x1) x2) => (__eo_to_smt_tuple_select (__eo_to_smt_type (__eo_typeof x2)) (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update x1) x2) x3) => (__eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof x2)) (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.set_empty x1) => (__eo_to_smt_set_empty (__eo_to_smt_type x1))
  | (Term.Apply Term.set_singleton x1) => (SmtTerm.set_singleton (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.set_union x1) x2) => (SmtTerm.set_union (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_inter x1) x2) => (SmtTerm.set_inter (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_minus x1) x2) => (SmtTerm.set_minus (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_member x1) x2) => (SmtTerm.set_member (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_subset x1) x2) => (SmtTerm.set_subset (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_choose x1) x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x1)))
    (SmtTerm.choice "_at_x" _v0 (SmtTerm.set_member (SmtTerm.Var "_at_x" _v0) (__eo_to_smt x1)))
  | (Term.Apply Term.set_is_empty x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.eq _v0 (SmtTerm.set_empty (__smtx_typeof _v0)))
  | (Term.Apply Term.set_is_singleton x1) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x1)))
    (SmtTerm.exists "_at_x" _v0 (SmtTerm.eq (__eo_to_smt x1) (SmtTerm.set_singleton (SmtTerm.Var "_at_x" _v0))))
  | (Term.Apply (Term.Apply Term.set_insert Term.__eo_List_nil) x1) => (__eo_to_smt x1)
  | (Term.Apply (Term.Apply Term.set_insert (Term.Apply (Term.Apply Term.__eo_List_cons x1) x2)) x3) => (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt x1)) (__eo_to_smt (Term.Apply (Term.Apply Term.set_insert x2) x3)))
  | (Term._at_sets_deq_diff x1 x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
    let _v2 := (SmtTerm.Var "_at_x" _v0)
    (SmtTerm.choice "_at_x" _v0 (SmtTerm.not (SmtTerm.eq (SmtTerm.set_member _v2 (__eo_to_smt x1)) (SmtTerm.set_member _v2 (__eo_to_smt x2)))))
  | (Term.Apply (Term.Apply Term.qdiv x1) x2) => (SmtTerm.qdiv (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.qdiv_total x1) x2) => (SmtTerm.qdiv_total (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term._at_div_by_zero x1) => (SmtTerm.qdiv (__eo_to_smt x1) (SmtTerm.Rational (native_mk_rational 0 1)))
  | (Term.Apply (Term.Apply Term.forall x1) x2) => (SmtTerm.not (__eo_to_smt_exists x1 (SmtTerm.not (__eo_to_smt x2))))
  | (Term.Apply (Term.Apply Term.exists x1) x2) => (__eo_to_smt_exists x1 (__eo_to_smt x2))
  | (Term._at_quantifiers_skolemize (Term.Apply (Term.Apply Term.forall x1) x2) x3) => (native_ite (native_teq (__eo_is_neg x3) (Term.Boolean false)) (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists x1 (SmtTerm.not (__eo_to_smt x2))) (__eo_to_smt_nat x3)) SmtTerm.None)
  | (Term.Apply (Term.Apply Term.int_to_bv x1) x2) => (SmtTerm.int_to_bv (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply Term.ubv_to_int x1) => (SmtTerm.ubv_to_int (__eo_to_smt x1))
  | (Term.Apply Term.sbv_to_int x1) => (SmtTerm.sbv_to_int (__eo_to_smt x1))
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.None




end

end

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of ObjectTerm.
-/
inductive eo_is_obj : Term -> ObjectTerm -> Prop
  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)



/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false in an object model.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (M : ObjectModel) (t : Term) (b : Bool) : Prop :=
  exists (s : ObjectTerm), (eo_is_obj t s) /\ (obj_interprets M s b)

/-
Eunoia satisfiability depends on SMT satisfiability.
-/
def eo_satisfiability (t : Term) (b : Bool) : Prop :=
  exists (s : ObjectTerm), (eo_is_obj t s) /\ (smt_satisfiability s b)


/- ---------------------------------------------- -/
