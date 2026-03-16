import Cpc.SmtModel
import Cpc.Logos

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
abbrev Object_Term := SmtTerm

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
abbrev obj_interprets := smt_interprets


/-
Definitions for eo_is_obj
-/
mutual

def __eo_to_smt_re_unfold_pos_component (s : SmtTerm) : SmtTerm -> smt_lit_Nat -> SmtTerm
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat r1) r2), smt_lit_nat_zero => 
    let _v0 := (SmtType.Seq SmtType.Char)
    let _v2 := (SmtTerm.Var "_at_x" _v0)
    let _v3 := (SmtTerm.Apply SmtTerm.str_len _v2)
    let _v4 := (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr s) _v3) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm.str_len s)) _v3))
    (SmtTerm.Apply (SmtTerm.choice "_at_x" _v0) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq s) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat _v2) _v4))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re _v2) r1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re _v4) r2))))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat r1) r2), (smt_lit_nat_succ n) => 
    let _v0 := (SmtTerm.Apply SmtTerm.str_len (__eo_to_smt_re_unfold_pos_component s (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat r1) r2) smt_lit_nat_zero))
    (__eo_to_smt_re_unfold_pos_component (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr s) _v0) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm.str_len s)) _v0)) r2 n)
  | r1, n => SmtTerm.None


def __eo_to_smt_quantifiers_skolemize : SmtTerm -> smt_lit_Nat -> SmtTerm
  | (SmtTerm.Apply (SmtTerm.exists s T) F), smt_lit_nat_zero => (SmtTerm.Apply (SmtTerm.choice s T) F)
  | (SmtTerm.Apply (SmtTerm.exists s T) F), (smt_lit_nat_succ n) => (__eo_to_smt_quantifiers_skolemize (__smtx_substitute s T (__eo_to_smt_quantifiers_skolemize (SmtTerm.Apply (SmtTerm.exists s T) F) smt_lit_nat_zero) F) n)
  | F, t => SmtTerm.None


def __eo_to_smt_type_tuple (U : SmtType) : SmtType -> SmtType
  | (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum c SmtDatatype.null)) => (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum (SmtDatatypeCons.cons U c) SmtDatatype.null))
  | T => SmtType.None


def __eo_to_smt_nat : Term -> smt_lit_Nat
  | (Term.Numeral n) => (smt_lit_int_to_nat n)
  | t => smt_lit_nat_zero


def __eo_to_smt_datatype_cons : DatatypeCons -> SmtDatatypeCons
  | DatatypeCons.unit => SmtDatatypeCons.unit
  | (DatatypeCons.cons U c) => (SmtDatatypeCons.cons (__eo_to_smt_type U) (__eo_to_smt_datatype_cons c))


def __eo_to_smt_datatype : Datatype -> SmtDatatype
  | (Datatype.sum c d) => (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
  | Datatype.null => SmtDatatype.null


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | (Term.DatatypeType s d) => (SmtType.Datatype s (__eo_to_smt_datatype d))
  | (Term.USort i) => (SmtType.USort i)
  | Term.Int => SmtType.Int
  | Term.Real => SmtType.Real
  | (Term.Apply Term.BitVec (Term.Numeral n1)) => (SmtType.BitVec n1)
  | Term.Char => SmtType.Char
  | (Term.Apply Term.Seq x1) => (SmtType.Seq (__eo_to_smt_type x1))
  | (Term.Apply (Term.Apply Term.Array x1) x2) => (SmtType.Map (__eo_to_smt_type x1) (__eo_to_smt_type x2))
  | Term.RegLan => SmtType.RegLan
  | Term.UnitTuple => (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
  | (Term.Apply (Term.Apply Term.Tuple x1) x2) => (__eo_to_smt_type_tuple (__eo_to_smt_type x1) (__eo_to_smt_type x2))
  | (Term.Apply Term.Set x1) => (SmtType.Map (__eo_to_smt_type x1) SmtType.Bool)
  | T => SmtType.None


def __eo_to_smt_tuple_app_extend : SmtTerm -> SmtType -> SmtTerm
  | (SmtTerm.Apply f a), T => (SmtTerm.Apply (__eo_to_smt_tuple_app_extend f T) a)
  | (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum c SmtDatatype.null) smt_lit_nat_zero), T => (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum (__smtx_dtc_concat c (SmtDatatypeCons.cons T SmtDatatypeCons.unit)) SmtDatatype.null) smt_lit_nat_zero)
  | s, T => SmtTerm.None


def __eo_to_smt_tuple_select : SmtType -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtType.Datatype "_at_Tuple" d), (SmtTerm.Numeral n), t => (smt_lit_ite (smt_lit_zleq 0 n) (SmtTerm.Apply (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero (smt_lit_int_to_nat n)) t) SmtTerm.None)
  | T, n, t => SmtTerm.None


def __eo_to_smt_tester : SmtTerm -> SmtTerm
  | (SmtTerm.DtCons s d n) => (SmtTerm.DtTester s d n)
  | t => SmtTerm.None


def __eo_to_smt_updater_rec : SmtTerm -> smt_lit_Nat -> SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtTerm.DtSel s d n m), smt_lit_nat_zero, t, u, acc => acc
  | (SmtTerm.DtSel s d n m), (smt_lit_nat_succ k), t, u, acc => 
    let _v0 := (SmtTerm.DtSel s d n m)
    (__eo_to_smt_updater_rec _v0 k t u (SmtTerm.Apply acc (smt_lit_ite (smt_lit_nateq m k) t (SmtTerm.Apply _v0 u))))
  | v, k, t, u, acc => SmtTerm.None


def __eo_to_smt_updater : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtTerm.DtSel s d n m), t, u => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.DtTester s d n) u)) (__eo_to_smt_updater_rec (SmtTerm.DtSel s d n m) (__smtx_dt_num_sels d n) t u (SmtTerm.DtCons s d n))) u)
  | sel, t, d => SmtTerm.None


def __eo_to_smt_tuple_update : SmtType -> SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm
  | (SmtType.Datatype "_at_Tuple" d), (SmtTerm.Numeral n), t, u => (smt_lit_ite (smt_lit_zleq 0 n) (__eo_to_smt_updater (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero (smt_lit_int_to_nat n)) t u) SmtTerm.None)
  | T, n, t, u => SmtTerm.None


def __eo_to_smt_exists : Term -> SmtTerm -> SmtTerm
  | Term.__eo_List_nil, F => F
  | (Term.Apply (Term.Apply Term.__eo_List (Term.Var s T)) vs), F => (SmtTerm.Apply (SmtTerm.exists s (__eo_to_smt_type T)) (__eo_to_smt_exists vs F))
  | vs, F => SmtTerm.None


def __eo_to_smt_lambda : Term -> SmtTerm -> SmtTerm
  | Term.__eo_List_nil, F => F
  | (Term.Apply (Term.Apply Term.__eo_List (Term.Var s T)) vs), F => (SmtTerm.Apply (SmtTerm.lambda s (__eo_to_smt_type T)) (__eo_to_smt_exists vs F))
  | vs, F => SmtTerm.None


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var s T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | (Term.DtCons s d i) => (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
  | (Term.DtSel s d i j) => (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j)
  | (Term.UConst i T) => (SmtTerm.UConst i (__eo_to_smt_type T))
  | (Term.Apply (Term.Apply (Term.Apply Term.ite x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply Term.not x1) => (SmtTerm.Apply SmtTerm.not (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.or x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.and x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.imp x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.xor x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.eq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.lambda x1) x2) => (__eo_to_smt_lambda x1 (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.distinct x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term._at_purify x1) => (__eo_to_smt x1)
  | (Term.Apply (Term.Apply Term.plus x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.neg x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mult x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.lt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.leq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.gt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.geq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.to_real x1) => (SmtTerm.Apply SmtTerm.to_real (__eo_to_smt x1))
  | (Term.Apply Term.to_int x1) => (SmtTerm.Apply SmtTerm.to_int (__eo_to_smt x1))
  | (Term.Apply Term.is_int x1) => (SmtTerm.Apply SmtTerm.is_int (__eo_to_smt x1))
  | (Term.Apply Term.abs x1) => (SmtTerm.Apply SmtTerm.abs (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.div x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mod x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.multmult x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.divisible x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.int_pow2 x1) => (SmtTerm.Apply SmtTerm.int_pow2 (__eo_to_smt x1))
  | (Term.Apply Term.int_log2 x1) => (SmtTerm.Apply SmtTerm.int_log2 (__eo_to_smt x1))
  | (Term.Apply Term.int_ispow2 x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq _v0) (SmtTerm.Numeral 0))) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq _v0) (SmtTerm.Apply SmtTerm.int_pow2 (SmtTerm.Apply SmtTerm.int_log2 _v0))))
  | (Term.Apply (Term.Apply Term.div_total x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.mod_total x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.multmult_total x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term._at_int_div_by_zero x1) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt x1)) (SmtTerm.Numeral 0))
  | (Term.Apply Term._at_mod_by_zero x1) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt x1)) (SmtTerm.Numeral 0))
  | (Term.Apply (Term.Apply Term.select x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.store x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term._at_array_deq_diff x1 x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
    let _v2 := (SmtTerm.Var "_at_x" _v0)
    (SmtTerm.Apply (SmtTerm.choice "_at_x" _v0) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1)) _v2)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x2)) _v2))))
  | (Term.Apply Term._at_bvsize x1) => (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x1))))
  | (Term.Apply (Term.Apply Term.concat x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.extract x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.repeat x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.bvnot x1) => (SmtTerm.Apply SmtTerm.bvnot (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvand x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvor x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvnand x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvnor x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvxor x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvxnor x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvcomp x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.bvneg x1) => (SmtTerm.Apply SmtTerm.bvneg (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvadd x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvmul x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvudiv x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvurem x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsub x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsdiv x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsrem x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsmod x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvult x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvule x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvugt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvuge x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvslt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsle x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsgt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsge x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvshl x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvlshr x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvashr x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.zero_extend x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.sign_extend x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.rotate_left x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.rotate_right x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.bvite x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x1)) (SmtTerm.Binary 1 1))) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.bvuaddo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.bvnego x1) => (SmtTerm.Apply SmtTerm.bvnego (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.bvsaddo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvumulo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsmulo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvusubo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvssubo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.bvsdivo x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.bvultbv x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult (__eo_to_smt x1)) (__eo_to_smt x2))) (SmtTerm.Binary 1 1)) (SmtTerm.Binary 1 0))
  | (Term.Apply (Term.Apply (Term.Apply Term.bvsltbv x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt (__eo_to_smt x1)) (__eo_to_smt x2))) (SmtTerm.Binary 1 1)) (SmtTerm.Binary 1 0))
  | (Term.Apply Term.bvredand x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0) (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)))
  | (Term.Apply Term.bvredor x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.Apply SmtTerm.bvnot (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0) (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)))
  | (Term.Apply (Term.Apply Term._at_bit x1) x2) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract _v0) _v0) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term._at_from_bools x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (__eo_to_smt x1)) (SmtTerm.Binary 1 1)) (SmtTerm.Binary 1 0))) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term._at_bv x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.seq_empty (Term.Apply Term.Seq Term.Char)) => (SmtTerm.String "")
  | (Term.seq_empty x1) => (SmtTerm.seq_empty (__eo_to_smt_type x1))
  | (Term.Apply Term.str_len x1) => (SmtTerm.Apply SmtTerm.str_len (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.str_concat x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_substr x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_contains x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_at x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_prefixof x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_suffixof x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.str_rev x1) => (SmtTerm.Apply SmtTerm.str_rev (__eo_to_smt x1))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_update x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply Term.str_to_lower x1) => (SmtTerm.Apply SmtTerm.str_to_lower (__eo_to_smt x1))
  | (Term.Apply Term.str_to_upper x1) => (SmtTerm.Apply SmtTerm.str_to_upper (__eo_to_smt x1))
  | (Term.Apply Term.str_to_code x1) => (SmtTerm.Apply SmtTerm.str_to_code (__eo_to_smt x1))
  | (Term.Apply Term.str_from_code x1) => (SmtTerm.Apply SmtTerm.str_from_code (__eo_to_smt x1))
  | (Term.Apply Term.str_is_digit x1) => (SmtTerm.Apply SmtTerm.str_is_digit (__eo_to_smt x1))
  | (Term.Apply Term.str_to_int x1) => (SmtTerm.Apply SmtTerm.str_to_int (__eo_to_smt x1))
  | (Term.Apply Term.str_from_int x1) => (SmtTerm.Apply SmtTerm.str_from_int (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.str_lt x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.str_leq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | Term.re_allchar => SmtTerm.re_allchar
  | Term.re_none => SmtTerm.re_none
  | Term.re_all => SmtTerm.re_all
  | (Term.Apply Term.str_to_re x1) => (SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt x1))
  | (Term.Apply Term.re_mult x1) => (SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt x1))
  | (Term.Apply Term.re_plus x1) => (SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.re_exp x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.re_opt x1) => (SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt x1))
  | (Term.Apply Term.re_comp x1) => (SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.re_range x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_concat x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_inter x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_union x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.re_diff x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.re_loop x1) x2) x3) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop (__eo_to_smt x1)) (__eo_to_smt x2)) (__eo_to_smt x3))
  | (Term.Apply (Term.Apply Term.str_in_re x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.seq_unit x1) => (SmtTerm.Apply SmtTerm.seq_unit (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.seq_nth x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term._at_re_unfold_pos_component x1) x2) x3) => (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt_nat x3))
  | (Term.Apply (Term.Apply Term._at_strings_deq_diff x1) x2) => 
    let _v0 := (SmtTerm.Numeral 1)
    let _v2 := (SmtTerm.Var "_at_x" SmtType.Int)
    (SmtTerm.Apply (SmtTerm.choice "_at_x" SmtType.Int) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt x1)) _v2) _v0)) (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt x2)) _v2) _v0))))
  | (Term.Apply (Term.Apply Term._at_strings_stoi_result x1) x2) => (SmtTerm.Apply SmtTerm.str_to_int (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt x1)) (SmtTerm.Numeral 0)) (__eo_to_smt x2)))
  | (Term.Apply Term._at_strings_stoi_non_digit x1) => (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt x1)) (SmtTerm.Apply SmtTerm.re_comp (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (SmtTerm.String "0")) (SmtTerm.String "9")))) (SmtTerm.Numeral 0))
  | (Term.Apply (Term.Apply Term._at_strings_itos_result x1) x2) => (SmtTerm.Apply SmtTerm.str_from_int (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt x1)) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult (SmtTerm.Numeral 10)) (__eo_to_smt x2))))
  | (Term.Apply (Term.Apply Term._at_strings_num_occur x1) x2) => 
    let _v0 := (__eo_to_smt x2)
    let _v1 := (__eo_to_smt x1)
    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm.str_len _v1)) (SmtTerm.Apply SmtTerm.str_len (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all _v1) _v0) (SmtTerm.String ""))))) (SmtTerm.Apply SmtTerm.str_len _v0))
  | (Term.Apply (Term.Apply (Term.Apply Term._at_witness_string_length x1) x2) x3) => 
    let _v0 := (__eo_to_smt_type x1)
    (SmtTerm.Apply (SmtTerm.choice "_at_x" _v0) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply SmtTerm.str_len (SmtTerm.Var "_at_x" _v0))) (__eo_to_smt x2)))
  | (Term.Apply Term.is x1) => (__eo_to_smt_tester (__eo_to_smt x1))
  | (Term.Apply (Term.Apply (Term.Apply Term.update x1) x2) x3) => (__eo_to_smt_updater (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | Term.tuple_unit => (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) smt_lit_nat_zero)
  | (Term.Apply (Term.Apply Term.tuple x1) x2) => (SmtTerm.Apply (__eo_to_smt_tuple_app_extend (__eo_to_smt x1) (__eo_to_smt_type (__eo_typeof x2))) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.tuple_select x1) x2) => (__eo_to_smt_tuple_select (__eo_to_smt_type (__eo_typeof x2)) (__eo_to_smt x1) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply (Term.Apply Term.tuple_update x1) x2) x3) => (__eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof x2)) (__eo_to_smt x1) (__eo_to_smt x2) (__eo_to_smt x3))
  | (Term.set_empty x1) => (SmtTerm.set_empty (__eo_to_smt_type x1))
  | (Term.Apply Term.set_singleton x1) => (SmtTerm.Apply SmtTerm.set_singleton (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.set_union x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_inter x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_minus x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_member x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_subset x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.set_choose x1) x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x1)))
    (SmtTerm.Apply (SmtTerm.choice "_at_x" _v0) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0)) (__eo_to_smt x1)))
  | (Term.Apply Term.set_is_empty x1) => 
    let _v0 := (__eo_to_smt x1)
    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq _v0) (SmtTerm.set_empty (__smtx_typeof _v0)))
  | (Term.Apply Term.set_is_singleton x1) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x1)))
    (SmtTerm.Apply (SmtTerm.exists "_at_x" _v0) (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x1)) (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" _v0))))
  | (Term.Apply (Term.Apply Term.set_insert Term.__eo_List_nil) x1) => (__eo_to_smt x1)
  | (Term.Apply (Term.Apply Term.set_insert (Term.Apply (Term.Apply Term.__eo_List_cons x1) x2)) x3) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union (SmtTerm.Apply SmtTerm.set_singleton (__eo_to_smt x1))) (__eo_to_smt (Term.Apply (Term.Apply Term.set_insert x2) x3)))
  | (Term._at_sets_deq_diff x1 x2) => 
    let _v0 := (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
    let _v2 := (SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0))
    (SmtTerm.Apply (SmtTerm.choice "_at_x" _v0) (SmtTerm.Apply SmtTerm.not (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply _v2 (__eo_to_smt x1))) (SmtTerm.Apply _v2 (__eo_to_smt x2)))))
  | (Term.Apply (Term.Apply Term.qdiv x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.qdiv_total x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term._at_div_by_zero x1) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt x1)) (SmtTerm.Rational (smt_lit_mk_rational 0 1)))
  | (Term.Apply (Term.Apply Term.forall x1) x2) => (SmtTerm.Apply SmtTerm.not (__eo_to_smt_exists x1 (SmtTerm.Apply SmtTerm.not (__eo_to_smt x2))))
  | (Term.Apply (Term.Apply Term.exists x1) x2) => (__eo_to_smt_exists x1 (__eo_to_smt x2))
  | (Term._at_quantifiers_skolemize (Term.Apply (Term.Apply Term.forall x1) x2) x3) => (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists x1 (SmtTerm.Apply SmtTerm.not (__eo_to_smt x2))) (__eo_to_smt_nat x3))
  | (Term.Apply (Term.Apply Term.int_to_bv x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply Term.ubv_to_int x1) => (SmtTerm.Apply SmtTerm.ubv_to_int (__eo_to_smt x1))
  | (Term.Apply Term.sbv_to_int x1) => (SmtTerm.Apply SmtTerm.sbv_to_int (__eo_to_smt x1))
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.None




end 

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of Object_Term.
-/
inductive eo_is_obj : Term -> Object_Term -> Prop
  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)


/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Object_Term), (eo_is_obj t s) /\ (obj_interprets s b)

/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
theorem correct___eo_prog_scope (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_scope x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_process_scope -/
theorem correct___eo_prog_process_scope (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_process_scope x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_eq -/
theorem correct___eo_prog_ite_eq (x1 : Term) :
  (Not (eo_interprets (__eo_prog_ite_eq x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_split -/
theorem correct___eo_prog_split (x1 : Term) :
  (Not (eo_interprets (__eo_prog_split x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_resolution -/
theorem correct___eo_prog_resolution (x1 x2 x3 x4 : Term) :
  (eo_interprets x3 true) ->
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_resolution x1 x2 (Proof.pf x3) (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_chain_resolution -/
theorem correct___eo_prog_chain_resolution (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_chain_resolution x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_chain_m_resolution -/
theorem correct___eo_prog_chain_m_resolution (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_chain_m_resolution x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_factoring -/
theorem correct___eo_prog_factoring (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_factoring (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_reordering -/
theorem correct___eo_prog_reordering (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_reordering x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_resolve -/
theorem correct___eo_prog_eq_resolve (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_modus_ponens -/
theorem correct___eo_prog_modus_ponens (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_not_elim -/
theorem correct___eo_prog_not_not_elim (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_not_elim (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_and_elim -/
theorem correct___eo_prog_and_elim (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_and_elim x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_and_intro -/
theorem correct___eo_prog_and_intro (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_and_intro (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_or_elim -/
theorem correct___eo_prog_not_or_elim (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_not_or_elim x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_implies_elim -/
theorem correct___eo_prog_implies_elim (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_implies_elim (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_implies_elim1 -/
theorem correct___eo_prog_not_implies_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_implies_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_implies_elim2 -/
theorem correct___eo_prog_not_implies_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_implies_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_equiv_elim1 -/
theorem correct___eo_prog_equiv_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_equiv_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_equiv_elim2 -/
theorem correct___eo_prog_equiv_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_equiv_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_equiv_elim1 -/
theorem correct___eo_prog_not_equiv_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_equiv_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_equiv_elim2 -/
theorem correct___eo_prog_not_equiv_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_equiv_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_xor_elim1 -/
theorem correct___eo_prog_xor_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_xor_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_xor_elim2 -/
theorem correct___eo_prog_xor_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_xor_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_xor_elim1 -/
theorem correct___eo_prog_not_xor_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_xor_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_xor_elim2 -/
theorem correct___eo_prog_not_xor_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_xor_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_elim1 -/
theorem correct___eo_prog_ite_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_ite_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_elim2 -/
theorem correct___eo_prog_ite_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_ite_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_ite_elim1 -/
theorem correct___eo_prog_not_ite_elim1 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_ite_elim1 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_ite_elim2 -/
theorem correct___eo_prog_not_ite_elim2 (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_ite_elim2 (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_not_and -/
theorem correct___eo_prog_not_and (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_not_and (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_and_pos -/
theorem correct___eo_prog_cnf_and_pos (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_and_pos x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_and_neg -/
theorem correct___eo_prog_cnf_and_neg (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_and_neg x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_or_pos -/
theorem correct___eo_prog_cnf_or_pos (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_or_pos x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_or_neg -/
theorem correct___eo_prog_cnf_or_neg (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_or_neg x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_pos -/
theorem correct___eo_prog_cnf_implies_pos (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_implies_pos x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_neg1 -/
theorem correct___eo_prog_cnf_implies_neg1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_implies_neg1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_neg2 -/
theorem correct___eo_prog_cnf_implies_neg2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_implies_neg2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_pos1 -/
theorem correct___eo_prog_cnf_equiv_pos1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_equiv_pos1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_pos2 -/
theorem correct___eo_prog_cnf_equiv_pos2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_equiv_pos2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_neg1 -/
theorem correct___eo_prog_cnf_equiv_neg1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_equiv_neg1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_neg2 -/
theorem correct___eo_prog_cnf_equiv_neg2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_equiv_neg2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_pos1 -/
theorem correct___eo_prog_cnf_xor_pos1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_xor_pos1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_pos2 -/
theorem correct___eo_prog_cnf_xor_pos2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_xor_pos2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_neg1 -/
theorem correct___eo_prog_cnf_xor_neg1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_xor_neg1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_neg2 -/
theorem correct___eo_prog_cnf_xor_neg2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_xor_neg2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos1 -/
theorem correct___eo_prog_cnf_ite_pos1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_pos1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos2 -/
theorem correct___eo_prog_cnf_ite_pos2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_pos2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos3 -/
theorem correct___eo_prog_cnf_ite_pos3 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_pos3 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg1 -/
theorem correct___eo_prog_cnf_ite_neg1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_neg1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg2 -/
theorem correct___eo_prog_cnf_ite_neg2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_neg2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg3 -/
theorem correct___eo_prog_cnf_ite_neg3 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_cnf_ite_neg3 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write -/
theorem correct___eo_prog_arrays_read_over_write (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_arrays_read_over_write x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write_contra -/
theorem correct___eo_prog_arrays_read_over_write_contra (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_arrays_read_over_write_contra (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write_1 -/
theorem correct___eo_prog_arrays_read_over_write_1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arrays_read_over_write_1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_ext -/
theorem correct___eo_prog_arrays_ext (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_arrays_ext (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_refl -/
theorem correct___eo_prog_refl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_refl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_symm (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_trans -/
theorem correct___eo_prog_trans (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_trans (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_cong -/
theorem correct___eo_prog_cong (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_cong x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_nary_cong -/
theorem correct___eo_prog_nary_cong (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_nary_cong x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_pairwise_cong -/
theorem correct___eo_prog_pairwise_cong (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_pairwise_cong x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_true_intro -/
theorem correct___eo_prog_true_intro (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_true_intro (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_true_elim -/
theorem correct___eo_prog_true_elim (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_true_elim (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_false_intro -/
theorem correct___eo_prog_false_intro (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_false_intro (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_false_elim -/
theorem correct___eo_prog_false_elim (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_false_elim (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ho_cong -/
theorem correct___eo_prog_ho_cong (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_ho_cong (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_elim -/
theorem correct___eo_prog_distinct_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_true -/
theorem correct___eo_prog_distinct_true (x1 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_true x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_false -/
theorem correct___eo_prog_distinct_false (x1 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_false x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_lambda_elim -/
theorem correct___eo_prog_lambda_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_lambda_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_sum_ub -/
theorem correct___eo_prog_arith_sum_ub (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_arith_sum_ub (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_pos -/
theorem correct___eo_prog_arith_mult_pos (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_mult_pos x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_neg -/
theorem correct___eo_prog_arith_mult_neg (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_mult_neg x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_trichotomy -/
theorem correct___eo_prog_arith_trichotomy (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_arith_trichotomy (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_int_tight_ub -/
theorem correct___eo_prog_int_tight_ub (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_int_tight_ub (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_int_tight_lb -/
theorem correct___eo_prog_int_tight_lb (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_int_tight_lb (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_tangent -/
theorem correct___eo_prog_arith_mult_tangent (x1 x2 x3 x4 x5 : Term) :
  (Not (eo_interprets (__eo_prog_arith_mult_tangent x1 x2 x3 x4 x5) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_sign -/
theorem correct___eo_prog_arith_mult_sign (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_mult_sign x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_abs_comparison -/
theorem correct___eo_prog_arith_mult_abs_comparison (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_arith_mult_abs_comparison (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_reduction -/
theorem correct___eo_prog_arith_reduction (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_reduction x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_poly_norm -/
theorem correct___eo_prog_arith_poly_norm (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_poly_norm x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_poly_norm_rel -/
theorem correct___eo_prog_arith_poly_norm_rel (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_arith_poly_norm_rel x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_repeat_elim -/
theorem correct___eo_prog_bv_repeat_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_repeat_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_smulo_elim -/
theorem correct___eo_prog_bv_smulo_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_smulo_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_umulo_elim -/
theorem correct___eo_prog_bv_umulo_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_umulo_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_bitwise_slicing -/
theorem correct___eo_prog_bv_bitwise_slicing (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_bitwise_slicing x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_bitblast_step -/
theorem correct___eo_prog_bv_bitblast_step (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_bitblast_step x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_poly_norm -/
theorem correct___eo_prog_bv_poly_norm (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_poly_norm x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_poly_norm_eq -/
theorem correct___eo_prog_bv_poly_norm_eq (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_bv_poly_norm_eq x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_length_pos -/
theorem correct___eo_prog_string_length_pos (x1 : Term) :
  (Not (eo_interprets (__eo_prog_string_length_pos x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_length_non_empty -/
theorem correct___eo_prog_string_length_non_empty (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_string_length_non_empty (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_eq -/
theorem correct___eo_prog_concat_eq (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_concat_eq x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_unify -/
theorem correct___eo_prog_concat_unify (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_concat_unify x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_csplit -/
theorem correct___eo_prog_concat_csplit (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_concat_csplit x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_split -/
theorem correct___eo_prog_concat_split (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_concat_split x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_lprop -/
theorem correct___eo_prog_concat_lprop (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_concat_lprop x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_cprop -/
theorem correct___eo_prog_concat_cprop (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_concat_cprop x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_decompose -/
theorem correct___eo_prog_string_decompose (x1 x2 x3 : Term) :
  (eo_interprets x2 true) ->
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_string_decompose x1 (Proof.pf x2) (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_exists_string_length -/
theorem correct___eo_prog_exists_string_length (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_exists_string_length x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_code_inj -/
theorem correct___eo_prog_string_code_inj (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_string_code_inj x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_seq_unit_inj -/
theorem correct___eo_prog_string_seq_unit_inj (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_string_seq_unit_inj (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter -/
theorem correct___eo_prog_re_inter (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_re_inter (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat -/
theorem correct___eo_prog_re_concat (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_re_concat (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_pos -/
theorem correct___eo_prog_re_unfold_pos (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_re_unfold_pos (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_neg_concat_fixed -/
theorem correct___eo_prog_re_unfold_neg_concat_fixed (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_re_unfold_neg_concat_fixed x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_neg -/
theorem correct___eo_prog_re_unfold_neg (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_re_unfold_neg (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_ext -/
theorem correct___eo_prog_string_ext (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_string_ext (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_reduction -/
theorem correct___eo_prog_string_reduction (x1 : Term) :
  (Not (eo_interprets (__eo_prog_string_reduction x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_string_eager_reduction -/
theorem correct___eo_prog_string_eager_reduction (x1 : Term) :
  (Not (eo_interprets (__eo_prog_string_eager_reduction x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_string_pred_entail -/
theorem correct___eo_prog_arith_string_pred_entail (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_string_pred_entail x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_string_pred_safe_approx -/
theorem correct___eo_prog_arith_string_pred_safe_approx (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_string_pred_safe_approx x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_eval -/
theorem correct___eo_prog_str_in_re_eval (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_eval x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_consume -/
theorem correct___eo_prog_str_in_re_consume (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_consume x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_loop_elim -/
theorem correct___eo_prog_re_loop_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_loop_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_eq_elim -/
theorem correct___eo_prog_re_eq_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_eq_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_inclusion -/
theorem correct___eo_prog_re_inter_inclusion (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_inter_inclusion x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_inclusion -/
theorem correct___eo_prog_re_union_inclusion (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_union_inclusion x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_concat_star_char -/
theorem correct___eo_prog_str_in_re_concat_star_char (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_concat_star_char x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_sigma -/
theorem correct___eo_prog_str_in_re_sigma (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_sigma x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_sigma_star -/
theorem correct___eo_prog_str_in_re_sigma_star (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_sigma_star x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_ctn_multiset_subset -/
theorem correct___eo_prog_str_ctn_multiset_subset (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_ctn_multiset_subset x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_split_ctn -/
theorem correct___eo_prog_str_overlap_split_ctn (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_overlap_split_ctn x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_ctn -/
theorem correct___eo_prog_str_overlap_endpoints_ctn (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_overlap_endpoints_ctn x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_indexof -/
theorem correct___eo_prog_str_overlap_endpoints_indexof (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_overlap_endpoints_indexof x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_replace -/
theorem correct___eo_prog_str_overlap_endpoints_replace (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_overlap_endpoints_replace x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_eval -/
theorem correct___eo_prog_str_indexof_re_eval (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_indexof_re_eval x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_eval -/
theorem correct___eo_prog_str_replace_re_eval (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_re_eval x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_all_eval -/
theorem correct___eo_prog_str_replace_re_all_eval (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_re_all_eval x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_eval_op -/
theorem correct___eo_prog_seq_eval_op (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_eval_op x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_singleton_inj -/
theorem correct___eo_prog_sets_singleton_inj (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_sets_singleton_inj (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_ext -/
theorem correct___eo_prog_sets_ext (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_sets_ext (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_eval_op -/
theorem correct___eo_prog_sets_eval_op (x1 : Term) :
  (Not (eo_interprets (__eo_prog_sets_eval_op x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_insert_elim -/
theorem correct___eo_prog_sets_insert_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_sets_insert_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ubv_to_int_elim -/
theorem correct___eo_prog_ubv_to_int_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_ubv_to_int_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_int_to_bv_elim -/
theorem correct___eo_prog_int_to_bv_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_int_to_bv_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_instantiate -/
theorem correct___eo_prog_instantiate (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_instantiate x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_skolemize -/
theorem correct___eo_prog_skolemize (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_skolemize (Proof.pf x1)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_skolem_intro -/
theorem correct___eo_prog_skolem_intro (x1 : Term) :
  (Not (eo_interprets (__eo_prog_skolem_intro x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_alpha_equiv -/
theorem correct___eo_prog_alpha_equiv (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_alpha_equiv x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_beta_reduce -/
theorem correct___eo_prog_beta_reduce (x1 : Term) :
  (Not (eo_interprets (__eo_prog_beta_reduce x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_var_reordering -/
theorem correct___eo_prog_quant_var_reordering (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_var_reordering x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_exists_elim -/
theorem correct___eo_prog_exists_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_exists_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_unused_vars -/
theorem correct___eo_prog_quant_unused_vars (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_unused_vars x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_merge_prenex -/
theorem correct___eo_prog_quant_merge_prenex (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_merge_prenex x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_and -/
theorem correct___eo_prog_quant_miniscope_and (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_miniscope_and x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_or -/
theorem correct___eo_prog_quant_miniscope_or (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_miniscope_or x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_ite -/
theorem correct___eo_prog_quant_miniscope_ite (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_miniscope_ite x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_var_elim_eq -/
theorem correct___eo_prog_quant_var_elim_eq (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_var_elim_eq x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_dt_split -/
theorem correct___eo_prog_quant_dt_split (x1 : Term) :
  (Not (eo_interprets (__eo_prog_quant_dt_split x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_split -/
theorem correct___eo_prog_dt_split (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_split x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_inst -/
theorem correct___eo_prog_dt_inst (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_inst x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_selector -/
theorem correct___eo_prog_dt_collapse_selector (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_collapse_selector x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_tester -/
theorem correct___eo_prog_dt_collapse_tester (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_collapse_tester x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_tester_singleton -/
theorem correct___eo_prog_dt_collapse_tester_singleton (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_collapse_tester_singleton x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cons_eq -/
theorem correct___eo_prog_dt_cons_eq (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_cons_eq x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cons_eq_clash -/
theorem correct___eo_prog_dt_cons_eq_clash (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_cons_eq_clash x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cycle -/
theorem correct___eo_prog_dt_cycle (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_cycle x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_updater -/
theorem correct___eo_prog_dt_collapse_updater (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_collapse_updater x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_updater_elim -/
theorem correct___eo_prog_dt_updater_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_dt_updater_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_div_total_zero_real -/
theorem correct___eo_prog_arith_div_total_zero_real (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_div_total_zero_real x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_div_total_zero_int -/
theorem correct___eo_prog_arith_div_total_zero_int (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_div_total_zero_int x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total -/
theorem correct___eo_prog_arith_int_div_total (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_div_total x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_one -/
theorem correct___eo_prog_arith_int_div_total_one (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_int_div_total_one x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_zero -/
theorem correct___eo_prog_arith_int_div_total_zero (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_int_div_total_zero x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_neg -/
theorem correct___eo_prog_arith_int_div_total_neg (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_div_total_neg x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total -/
theorem correct___eo_prog_arith_int_mod_total (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_mod_total x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_one -/
theorem correct___eo_prog_arith_int_mod_total_one (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_int_mod_total_one x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_zero -/
theorem correct___eo_prog_arith_int_mod_total_zero (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_int_mod_total_zero x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_neg -/
theorem correct___eo_prog_arith_int_mod_total_neg (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_mod_total_neg x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_gt -/
theorem correct___eo_prog_arith_elim_gt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_elim_gt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_lt -/
theorem correct___eo_prog_arith_elim_lt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_elim_lt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_int_gt -/
theorem correct___eo_prog_arith_elim_int_gt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_elim_int_gt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_int_lt -/
theorem correct___eo_prog_arith_elim_int_lt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_elim_int_lt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_leq -/
theorem correct___eo_prog_arith_elim_leq (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_elim_leq x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_leq_norm -/
theorem correct___eo_prog_arith_leq_norm (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_leq_norm x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_tighten -/
theorem correct___eo_prog_arith_geq_tighten (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_geq_tighten x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_norm1_int -/
theorem correct___eo_prog_arith_geq_norm1_int (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_geq_norm1_int x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_norm1_real -/
theorem correct___eo_prog_arith_geq_norm1_real (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_geq_norm1_real x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_eq_elim_real -/
theorem correct___eo_prog_arith_eq_elim_real (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_eq_elim_real x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_eq_elim_int -/
theorem correct___eo_prog_arith_eq_elim_int (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_eq_elim_int x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_to_int_elim_to_real -/
theorem correct___eo_prog_arith_to_int_elim_to_real (x1 : Term) :
  (Not (eo_interprets (__eo_prog_arith_to_int_elim_to_real x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod_1 -/
theorem correct___eo_prog_arith_mod_over_mod_1 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_mod_over_mod_1 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod -/
theorem correct___eo_prog_arith_mod_over_mod (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_arith_mod_over_mod x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod_mult -/
theorem correct___eo_prog_arith_mod_over_mod_mult (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_arith_mod_over_mod_mult x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_eq_conflict -/
theorem correct___eo_prog_arith_int_eq_conflict (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_eq_conflict x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_geq_tighten -/
theorem correct___eo_prog_arith_int_geq_tighten (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_arith_int_geq_tighten x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_divisible_elim -/
theorem correct___eo_prog_arith_divisible_elim (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_arith_divisible_elim x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_eq -/
theorem correct___eo_prog_arith_abs_eq (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_abs_eq x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_int_gt -/
theorem correct___eo_prog_arith_abs_int_gt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_abs_int_gt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_real_gt -/
theorem correct___eo_prog_arith_abs_real_gt (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_abs_real_gt x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_ite_lift -/
theorem correct___eo_prog_arith_geq_ite_lift (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_arith_geq_ite_lift x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_leq_ite_lift -/
theorem correct___eo_prog_arith_leq_ite_lift (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_arith_leq_ite_lift x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_min_lt1 -/
theorem correct___eo_prog_arith_min_lt1 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_min_lt1 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_min_lt2 -/
theorem correct___eo_prog_arith_min_lt2 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_min_lt2 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_max_geq1 -/
theorem correct___eo_prog_arith_max_geq1 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_max_geq1 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_max_geq2 -/
theorem correct___eo_prog_arith_max_geq2 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_arith_max_geq2 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write -/
theorem correct___eo_prog_array_read_over_write (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_array_read_over_write x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write2 -/
theorem correct___eo_prog_array_read_over_write2 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_array_read_over_write2 x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_overwrite -/
theorem correct___eo_prog_array_store_overwrite (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_array_store_overwrite x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_self -/
theorem correct___eo_prog_array_store_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_array_store_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write_split -/
theorem correct___eo_prog_array_read_over_write_split (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_array_read_over_write_split x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_swap -/
theorem correct___eo_prog_array_store_swap (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_array_store_swap x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_double_not_elim -/
theorem correct___eo_prog_bool_double_not_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_double_not_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_true -/
theorem correct___eo_prog_bool_not_true (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_bool_not_true x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_false -/
theorem correct___eo_prog_bool_not_false (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_bool_not_false x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_true -/
theorem correct___eo_prog_bool_eq_true (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_eq_true x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_false -/
theorem correct___eo_prog_bool_eq_false (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_eq_false x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_nrefl -/
theorem correct___eo_prog_bool_eq_nrefl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_eq_nrefl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_false1 -/
theorem correct___eo_prog_bool_impl_false1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_impl_false1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_false2 -/
theorem correct___eo_prog_bool_impl_false2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_impl_false2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_true1 -/
theorem correct___eo_prog_bool_impl_true1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_impl_true1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_true2 -/
theorem correct___eo_prog_bool_impl_true2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_impl_true2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_elim -/
theorem correct___eo_prog_bool_impl_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_impl_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_dual_impl_eq -/
theorem correct___eo_prog_bool_dual_impl_eq (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_dual_impl_eq x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_conf -/
theorem correct___eo_prog_bool_and_conf (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bool_and_conf x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_conf2 -/
theorem correct___eo_prog_bool_and_conf2 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bool_and_conf2 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_taut -/
theorem correct___eo_prog_bool_or_taut (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bool_or_taut x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_taut2 -/
theorem correct___eo_prog_bool_or_taut2 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bool_or_taut2 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_de_morgan -/
theorem correct___eo_prog_bool_or_de_morgan (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bool_or_de_morgan x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_implies_de_morgan -/
theorem correct___eo_prog_bool_implies_de_morgan (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_implies_de_morgan x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_de_morgan -/
theorem correct___eo_prog_bool_and_de_morgan (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bool_and_de_morgan x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_and_distrib -/
theorem correct___eo_prog_bool_or_and_distrib (x1 x2 x3 x4 x5 : Term) :
  (Not (eo_interprets (__eo_prog_bool_or_and_distrib x1 x2 x3 x4 x5) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_implies_or_distrib -/
theorem correct___eo_prog_bool_implies_or_distrib (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bool_implies_or_distrib x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_refl -/
theorem correct___eo_prog_bool_xor_refl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_refl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_nrefl -/
theorem correct___eo_prog_bool_xor_nrefl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_nrefl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_false -/
theorem correct___eo_prog_bool_xor_false (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_false x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_true -/
theorem correct___eo_prog_bool_xor_true (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_true x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_comm -/
theorem correct___eo_prog_bool_xor_comm (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_comm x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_elim -/
theorem correct___eo_prog_bool_xor_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_xor_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_xor_elim -/
theorem correct___eo_prog_bool_not_xor_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_not_xor_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_eq_elim1 -/
theorem correct___eo_prog_bool_not_eq_elim1 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_not_eq_elim1 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_eq_elim2 -/
theorem correct___eo_prog_bool_not_eq_elim2 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bool_not_eq_elim2 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_neg_branch -/
theorem correct___eo_prog_ite_neg_branch (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_ite_neg_branch x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_true -/
theorem correct___eo_prog_ite_then_true (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_true x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_false -/
theorem correct___eo_prog_ite_else_false (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_false x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_false -/
theorem correct___eo_prog_ite_then_false (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_false x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_true -/
theorem correct___eo_prog_ite_else_true (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_true x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead_self -/
theorem correct___eo_prog_ite_then_lookahead_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_lookahead_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead_self -/
theorem correct___eo_prog_ite_else_lookahead_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_lookahead_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead_not_self -/
theorem correct___eo_prog_ite_then_lookahead_not_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_lookahead_not_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead_not_self -/
theorem correct___eo_prog_ite_else_lookahead_not_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_lookahead_not_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_expand -/
theorem correct___eo_prog_ite_expand (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_ite_expand x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_ite_elim -/
theorem correct___eo_prog_bool_not_ite_elim (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bool_not_ite_elim x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_true_cond -/
theorem correct___eo_prog_ite_true_cond (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_true_cond x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_false_cond -/
theorem correct___eo_prog_ite_false_cond (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_false_cond x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_not_cond -/
theorem correct___eo_prog_ite_not_cond (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_ite_not_cond x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_eq_branch -/
theorem correct___eo_prog_ite_eq_branch (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_ite_eq_branch x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead -/
theorem correct___eo_prog_ite_then_lookahead (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_lookahead x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead -/
theorem correct___eo_prog_ite_else_lookahead (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_lookahead x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_neg_lookahead -/
theorem correct___eo_prog_ite_then_neg_lookahead (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_ite_then_neg_lookahead x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_neg_lookahead -/
theorem correct___eo_prog_ite_else_neg_lookahead (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_ite_else_neg_lookahead x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_concat_extract_merge -/
theorem correct___eo_prog_bv_concat_extract_merge (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_concat_extract_merge x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_extract -/
theorem correct___eo_prog_bv_extract_extract (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_extract x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_whole -/
theorem correct___eo_prog_bv_extract_whole (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_whole x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_1 -/
theorem correct___eo_prog_bv_extract_concat_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_concat_1 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_2 -/
theorem correct___eo_prog_bv_extract_concat_2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_concat_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_3 -/
theorem correct___eo_prog_bv_extract_concat_3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_concat_3 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_4 -/
theorem correct___eo_prog_bv_extract_concat_4 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_concat_4 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim1 -/
theorem correct___eo_prog_bv_eq_extract_elim1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (eo_interprets x12 true) ->
  (Not (eo_interprets (__eo_prog_bv_eq_extract_elim1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim2 -/
theorem correct___eo_prog_bv_eq_extract_elim2 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_eq_extract_elim2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim3 -/
theorem correct___eo_prog_bv_eq_extract_elim3 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_eq_extract_elim3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_not -/
theorem correct___eo_prog_bv_extract_not (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bv_extract_not x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_1 -/
theorem correct___eo_prog_bv_extract_sign_extend_1 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_2 -/
theorem correct___eo_prog_bv_extract_sign_extend_2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_sign_extend_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_3 -/
theorem correct___eo_prog_bv_extract_sign_extend_3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_sign_extend_3 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_xor -/
theorem correct___eo_prog_bv_not_xor (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bv_not_xor x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_simplify_1 -/
theorem correct___eo_prog_bv_and_simplify_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_and_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_simplify_2 -/
theorem correct___eo_prog_bv_and_simplify_2 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_and_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_simplify_1 -/
theorem correct___eo_prog_bv_or_simplify_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_or_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_simplify_2 -/
theorem correct___eo_prog_bv_or_simplify_2 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_or_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_1 -/
theorem correct___eo_prog_bv_xor_simplify_1 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_xor_simplify_1 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_2 -/
theorem correct___eo_prog_bv_xor_simplify_2 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_xor_simplify_2 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_3 -/
theorem correct___eo_prog_bv_xor_simplify_3 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_xor_simplify_3 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_add_one -/
theorem correct___eo_prog_bv_ult_add_one (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_ult_add_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_slt_mult_1 -/
theorem correct___eo_prog_bv_mult_slt_mult_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_mult_slt_mult_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_slt_mult_2 -/
theorem correct___eo_prog_bv_mult_slt_mult_2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_mult_slt_mult_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_xor -/
theorem correct___eo_prog_bv_commutative_xor (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_commutative_xor x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_comp -/
theorem correct___eo_prog_bv_commutative_comp (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_commutative_comp x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eliminate_0 -/
theorem correct___eo_prog_bv_zero_extend_eliminate_0 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_zero_extend_eliminate_0 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eliminate_0 -/
theorem correct___eo_prog_bv_sign_extend_eliminate_0 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sign_extend_eliminate_0 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_neq -/
theorem correct___eo_prog_bv_not_neq (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_bv_not_neq x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_ones -/
theorem correct___eo_prog_bv_ult_ones (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_ult_ones x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_concat_merge_const -/
theorem correct___eo_prog_bv_concat_merge_const (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_concat_merge_const x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_add -/
theorem correct___eo_prog_bv_commutative_add (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_commutative_add x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sub_eliminate -/
theorem correct___eo_prog_bv_sub_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sub_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_width_one -/
theorem correct___eo_prog_bv_ite_width_one (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_width_one x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_width_one_not -/
theorem correct___eo_prog_bv_ite_width_one_not (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_width_one_not x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_xor_solve -/
theorem correct___eo_prog_bv_eq_xor_solve (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_bv_eq_xor_solve x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_not_solve -/
theorem correct___eo_prog_bv_eq_not_solve (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_eq_not_solve x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ugt_eliminate -/
theorem correct___eo_prog_bv_ugt_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ugt_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_uge_eliminate -/
theorem correct___eo_prog_bv_uge_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_uge_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sgt_eliminate -/
theorem correct___eo_prog_bv_sgt_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sgt_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sge_eliminate -/
theorem correct___eo_prog_bv_sge_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sge_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sle_eliminate -/
theorem correct___eo_prog_bv_sle_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sle_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_redor_eliminate -/
theorem correct___eo_prog_bv_redor_eliminate (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_redor_eliminate x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_redand_eliminate -/
theorem correct___eo_prog_bv_redand_eliminate (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_redand_eliminate x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_eliminate -/
theorem correct___eo_prog_bv_ule_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ule_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_comp_eliminate -/
theorem correct___eo_prog_bv_comp_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_comp_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_left_eliminate_1 -/
theorem correct___eo_prog_bv_rotate_left_eliminate_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_rotate_left_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_left_eliminate_2 -/
theorem correct___eo_prog_bv_rotate_left_eliminate_2 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_rotate_left_eliminate_2 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_right_eliminate_1 -/
theorem correct___eo_prog_bv_rotate_right_eliminate_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_rotate_right_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_right_eliminate_2 -/
theorem correct___eo_prog_bv_rotate_right_eliminate_2 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_rotate_right_eliminate_2 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nand_eliminate -/
theorem correct___eo_prog_bv_nand_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_nand_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nor_eliminate -/
theorem correct___eo_prog_bv_nor_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_nor_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xnor_eliminate -/
theorem correct___eo_prog_bv_xnor_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_xnor_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sdiv_eliminate -/
theorem correct___eo_prog_bv_sdiv_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_sdiv_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eliminate -/
theorem correct___eo_prog_bv_zero_extend_eliminate (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_zero_extend_eliminate x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_uaddo_eliminate -/
theorem correct___eo_prog_bv_uaddo_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_uaddo_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_saddo_eliminate -/
theorem correct___eo_prog_bv_saddo_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_saddo_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sdivo_eliminate -/
theorem correct___eo_prog_bv_sdivo_eliminate (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_sdivo_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_smod_eliminate -/
theorem correct___eo_prog_bv_smod_eliminate (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_smod_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_srem_eliminate -/
theorem correct___eo_prog_bv_srem_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_srem_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_usubo_eliminate -/
theorem correct___eo_prog_bv_usubo_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_usubo_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ssubo_eliminate -/
theorem correct___eo_prog_bv_ssubo_eliminate (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_ssubo_eliminate x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nego_eliminate -/
theorem correct___eo_prog_bv_nego_eliminate (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_nego_eliminate x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_children -/
theorem correct___eo_prog_bv_ite_equal_children (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_equal_children x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_const_children_1 -/
theorem correct___eo_prog_bv_ite_const_children_1 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_const_children_1 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_const_children_2 -/
theorem correct___eo_prog_bv_ite_const_children_2 (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_const_children_2 x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_1 -/
theorem correct___eo_prog_bv_ite_equal_cond_1 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_equal_cond_1 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_2 -/
theorem correct___eo_prog_bv_ite_equal_cond_2 (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_equal_cond_2 x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_3 -/
theorem correct___eo_prog_bv_ite_equal_cond_3 (x1 x2 x3 x4 x5 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_equal_cond_3 x1 x2 x3 x4 x5) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_then_if -/
theorem correct___eo_prog_bv_ite_merge_then_if (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_merge_then_if x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_else_if -/
theorem correct___eo_prog_bv_ite_merge_else_if (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_merge_else_if x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_then_else -/
theorem correct___eo_prog_bv_ite_merge_then_else (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_merge_then_else x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_else_else -/
theorem correct___eo_prog_bv_ite_merge_else_else (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ite_merge_else_else x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_0 -/
theorem correct___eo_prog_bv_shl_by_const_0 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_shl_by_const_0 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_1 -/
theorem correct___eo_prog_bv_shl_by_const_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_shl_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_2 -/
theorem correct___eo_prog_bv_shl_by_const_2 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_shl_by_const_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_0 -/
theorem correct___eo_prog_bv_lshr_by_const_0 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_lshr_by_const_0 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_1 -/
theorem correct___eo_prog_bv_lshr_by_const_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_lshr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_2 -/
theorem correct___eo_prog_bv_lshr_by_const_2 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_bv_lshr_by_const_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_0 -/
theorem correct___eo_prog_bv_ashr_by_const_0 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ashr_by_const_0 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_1 -/
theorem correct___eo_prog_bv_ashr_by_const_1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_ashr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_2 -/
theorem correct___eo_prog_bv_ashr_by_const_2 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_ashr_by_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup -/
theorem correct___eo_prog_bv_and_concat_pullup (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_and_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup -/
theorem correct___eo_prog_bv_or_concat_pullup (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_or_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup -/
theorem correct___eo_prog_bv_xor_concat_pullup (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_xor_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup2 -/
theorem correct___eo_prog_bv_and_concat_pullup2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_and_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup2 -/
theorem correct___eo_prog_bv_or_concat_pullup2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_or_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup2 -/
theorem correct___eo_prog_bv_xor_concat_pullup2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (Not (eo_interprets (__eo_prog_bv_xor_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup3 -/
theorem correct___eo_prog_bv_and_concat_pullup3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets x11 true) ->
  (eo_interprets x12 true) ->
  (eo_interprets x13 true) ->
  (eo_interprets x14 true) ->
  (eo_interprets x15 true) ->
  (Not (eo_interprets (__eo_prog_bv_and_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup3 -/
theorem correct___eo_prog_bv_or_concat_pullup3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets x11 true) ->
  (eo_interprets x12 true) ->
  (eo_interprets x13 true) ->
  (eo_interprets x14 true) ->
  (eo_interprets x15 true) ->
  (Not (eo_interprets (__eo_prog_bv_or_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup3 -/
theorem correct___eo_prog_bv_xor_concat_pullup3 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets x11 true) ->
  (eo_interprets x12 true) ->
  (eo_interprets x13 true) ->
  (eo_interprets x14 true) ->
  (eo_interprets x15 true) ->
  (Not (eo_interprets (__eo_prog_bv_xor_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_duplicate -/
theorem correct___eo_prog_bv_xor_duplicate (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_xor_duplicate x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_ones -/
theorem correct___eo_prog_bv_xor_ones (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_bv_xor_ones x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_not -/
theorem correct___eo_prog_bv_xor_not (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_xor_not x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_idemp -/
theorem correct___eo_prog_bv_not_idemp (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_not_idemp x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_zero_1 -/
theorem correct___eo_prog_bv_ult_zero_1 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ult_zero_1 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_zero_2 -/
theorem correct___eo_prog_bv_ult_zero_2 (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ult_zero_2 x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_self -/
theorem correct___eo_prog_bv_ult_self (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ult_self x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lt_self -/
theorem correct___eo_prog_bv_lt_self (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_lt_self x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_self -/
theorem correct___eo_prog_bv_ule_self (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ule_self x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_zero -/
theorem correct___eo_prog_bv_ule_zero (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ule_zero x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_ule -/
theorem correct___eo_prog_bv_zero_ule (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_zero_ule x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sle_self -/
theorem correct___eo_prog_bv_sle_self (x1 : Term) :
  (Not (eo_interprets (__eo_prog_bv_sle_self x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_max -/
theorem correct___eo_prog_bv_ule_max (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_bv_ule_max x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_ult -/
theorem correct___eo_prog_bv_not_ult (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_not_ult x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_1 -/
theorem correct___eo_prog_bv_mult_pow2_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_mult_pow2_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_2 -/
theorem correct___eo_prog_bv_mult_pow2_2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_mult_pow2_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_2b -/
theorem correct___eo_prog_bv_mult_pow2_2b (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_mult_pow2_2b x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_mult_leading_bit -/
theorem correct___eo_prog_bv_extract_mult_leading_bit (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Term) :
  (eo_interprets x10 true) ->
  (eo_interprets x11 true) ->
  (eo_interprets x12 true) ->
  (Not (eo_interprets (__eo_prog_bv_extract_mult_leading_bit x1 x2 x3 x4 x5 x6 x7 x8 x9 (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_pow2_not_one -/
theorem correct___eo_prog_bv_udiv_pow2_not_one (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_udiv_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_zero -/
theorem correct___eo_prog_bv_udiv_zero (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_udiv_zero x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_one -/
theorem correct___eo_prog_bv_udiv_one (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_udiv_one x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_pow2_not_one -/
theorem correct___eo_prog_bv_urem_pow2_not_one (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_bv_urem_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_one -/
theorem correct___eo_prog_bv_urem_one (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_urem_one x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_self -/
theorem correct___eo_prog_bv_urem_self (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_urem_self x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_zero -/
theorem correct___eo_prog_bv_shl_zero (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_shl_zero x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_zero -/
theorem correct___eo_prog_bv_lshr_zero (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_lshr_zero x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_zero -/
theorem correct___eo_prog_bv_ashr_zero (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_bv_ashr_zero x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ugt_urem -/
theorem correct___eo_prog_bv_ugt_urem (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_bv_ugt_urem x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_one -/
theorem correct___eo_prog_bv_ult_one (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_bv_ult_one x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_merge_sign_extend_1 -/
theorem correct___eo_prog_bv_merge_sign_extend_1 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_bv_merge_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_merge_sign_extend_2 -/
theorem correct___eo_prog_bv_merge_sign_extend_2 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_bv_merge_sign_extend_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eq_const_1 -/
theorem correct___eo_prog_bv_sign_extend_eq_const_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_eq_const_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eq_const_2 -/
theorem correct___eo_prog_bv_sign_extend_eq_const_2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_eq_const_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eq_const_1 -/
theorem correct___eo_prog_bv_zero_extend_eq_const_1 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_zero_extend_eq_const_1 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eq_const_2 -/
theorem correct___eo_prog_bv_zero_extend_eq_const_2 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_zero_extend_eq_const_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_ult_const_1 -/
theorem correct___eo_prog_bv_zero_extend_ult_const_1 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_zero_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_ult_const_2 -/
theorem correct___eo_prog_bv_zero_extend_ult_const_2 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_zero_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_1 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_1 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_2 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_2 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_3 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_3 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_ult_const_3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_4 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_4 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_bv_sign_extend_ult_const_4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_eq_singleton_emp -/
theorem correct___eo_prog_sets_eq_singleton_emp (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_eq_singleton_emp x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_member_singleton -/
theorem correct___eo_prog_sets_member_singleton (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_member_singleton x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_member_emp -/
theorem correct___eo_prog_sets_member_emp (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_member_emp x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_subset_elim -/
theorem correct___eo_prog_sets_subset_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_subset_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_comm -/
theorem correct___eo_prog_sets_union_comm (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_union_comm x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_comm -/
theorem correct___eo_prog_sets_inter_comm (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_inter_comm x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_emp1 -/
theorem correct___eo_prog_sets_inter_emp1 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_inter_emp1 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_emp2 -/
theorem correct___eo_prog_sets_inter_emp2 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_inter_emp2 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_emp1 -/
theorem correct___eo_prog_sets_minus_emp1 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_minus_emp1 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_emp2 -/
theorem correct___eo_prog_sets_minus_emp2 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_minus_emp2 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_emp1 -/
theorem correct___eo_prog_sets_union_emp1 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_union_emp1 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_emp2 -/
theorem correct___eo_prog_sets_union_emp2 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_sets_union_emp2 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_member -/
theorem correct___eo_prog_sets_inter_member (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_sets_inter_member x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_member -/
theorem correct___eo_prog_sets_minus_member (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_sets_minus_member x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_member -/
theorem correct___eo_prog_sets_union_member (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_sets_union_member x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_choose_singleton -/
theorem correct___eo_prog_sets_choose_singleton (x1 : Term) :
  (Not (eo_interprets (__eo_prog_sets_choose_singleton x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_self -/
theorem correct___eo_prog_sets_minus_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_minus_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_is_empty_elim -/
theorem correct___eo_prog_sets_is_empty_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_sets_is_empty_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_is_singleton_elim -/
theorem correct___eo_prog_sets_is_singleton_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_sets_is_singleton_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_false -/
theorem correct___eo_prog_str_eq_ctn_false (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_ctn_false x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_full_false1 -/
theorem correct___eo_prog_str_eq_ctn_full_false1 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_ctn_full_false1 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_full_false2 -/
theorem correct___eo_prog_str_eq_ctn_full_false2 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_ctn_full_false2 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_len_false -/
theorem correct___eo_prog_str_eq_len_false (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_len_false x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_str -/
theorem correct___eo_prog_str_substr_empty_str (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_empty_str x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_range -/
theorem correct___eo_prog_str_substr_empty_range (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_empty_range x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_start -/
theorem correct___eo_prog_str_substr_empty_start (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_empty_start x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_start_neg -/
theorem correct___eo_prog_str_substr_empty_start_neg (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_empty_start_neg x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_substr_start_geq_len -/
theorem correct___eo_prog_str_substr_substr_start_geq_len (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_substr_start_geq_len x1 x2 x3 x4 x5 x6 (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_eq_empty -/
theorem correct___eo_prog_str_substr_eq_empty (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_eq_empty x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_z_eq_empty_leq -/
theorem correct___eo_prog_str_substr_z_eq_empty_leq (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_z_eq_empty_leq x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_eq_empty_leq_len -/
theorem correct___eo_prog_str_substr_eq_empty_leq_len (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_eq_empty_leq_len x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_replace_inv -/
theorem correct___eo_prog_str_len_replace_inv (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_len_replace_inv x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_replace_all_inv -/
theorem correct___eo_prog_str_len_replace_all_inv (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_len_replace_all_inv x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_update_inv -/
theorem correct___eo_prog_str_len_update_inv (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_len_update_inv x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_update_in_first_concat -/
theorem correct___eo_prog_str_update_in_first_concat (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (eo_interprets x10 true) ->
  (Not (eo_interprets (__eo_prog_str_update_in_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_substr_in_range -/
theorem correct___eo_prog_str_len_substr_in_range (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_len_substr_in_range x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash -/
theorem correct___eo_prog_str_concat_clash (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_concat_clash x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash_rev -/
theorem correct___eo_prog_str_concat_clash_rev (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_concat_clash_rev x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash2 -/
theorem correct___eo_prog_str_concat_clash2 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_concat_clash2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash2_rev -/
theorem correct___eo_prog_str_concat_clash2_rev (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_concat_clash2_rev x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify -/
theorem correct___eo_prog_str_concat_unify (x1 x2 x3 x4 x5 : Term) :
  (Not (eo_interprets (__eo_prog_str_concat_unify x1 x2 x3 x4 x5) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_rev -/
theorem correct___eo_prog_str_concat_unify_rev (x1 x2 x3 x4 x5 : Term) :
  (Not (eo_interprets (__eo_prog_str_concat_unify_rev x1 x2 x3 x4 x5) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_base -/
theorem correct___eo_prog_str_concat_unify_base (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_concat_unify_base x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_base_rev -/
theorem correct___eo_prog_str_concat_unify_base_rev (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_concat_unify_base_rev x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_elim -/
theorem correct___eo_prog_str_prefixof_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_prefixof_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_elim -/
theorem correct___eo_prog_str_suffixof_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_suffixof_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_eq -/
theorem correct___eo_prog_str_prefixof_eq (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_prefixof_eq x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_eq -/
theorem correct___eo_prog_str_suffixof_eq (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_suffixof_eq x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_one -/
theorem correct___eo_prog_str_prefixof_one (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_prefixof_one x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_one -/
theorem correct___eo_prog_str_suffixof_one (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_suffixof_one x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine1 -/
theorem correct___eo_prog_str_substr_combine1 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_combine1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine2 -/
theorem correct___eo_prog_str_substr_combine2 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_combine2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine3 -/
theorem correct___eo_prog_str_substr_combine3 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_combine3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine4 -/
theorem correct___eo_prog_str_substr_combine4 (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_combine4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_concat1 -/
theorem correct___eo_prog_str_substr_concat1 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_concat1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_concat2 -/
theorem correct___eo_prog_str_substr_concat2 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_concat2 x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_replace -/
theorem correct___eo_prog_str_substr_replace (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_replace x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_full -/
theorem correct___eo_prog_str_substr_full (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_full x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_full_eq -/
theorem correct___eo_prog_str_substr_full_eq (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_full_eq x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_refl -/
theorem correct___eo_prog_str_contains_refl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_contains_refl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_concat_find -/
theorem correct___eo_prog_str_contains_concat_find (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_concat_find x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_concat_find_contra -/
theorem correct___eo_prog_str_contains_concat_find_contra (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_concat_find_contra x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_split_char -/
theorem correct___eo_prog_str_contains_split_char (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_split_char x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_leq_len_eq -/
theorem correct___eo_prog_str_contains_leq_len_eq (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_leq_len_eq x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_emp -/
theorem correct___eo_prog_str_contains_emp (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_emp x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_char -/
theorem correct___eo_prog_str_contains_char (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_char x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_at_elim -/
theorem correct___eo_prog_str_at_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_at_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_self -/
theorem correct___eo_prog_str_replace_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_id -/
theorem correct___eo_prog_str_replace_id (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_id x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_prefix -/
theorem correct___eo_prog_str_replace_prefix (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_prefix x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_no_contains -/
theorem correct___eo_prog_str_replace_no_contains (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_no_contains x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_base -/
theorem correct___eo_prog_str_replace_find_base (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_find_base x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_first_concat -/
theorem correct___eo_prog_str_replace_find_first_concat (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (eo_interprets x9 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_find_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_empty -/
theorem correct___eo_prog_str_replace_empty (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_empty x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_one_pre -/
theorem correct___eo_prog_str_replace_one_pre (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_one_pre x1 x2 x3 x4 x5 (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_pre -/
theorem correct___eo_prog_str_replace_find_pre (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_find_pre x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_no_contains -/
theorem correct___eo_prog_str_replace_all_no_contains (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_all_no_contains x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_empty -/
theorem correct___eo_prog_str_replace_all_empty (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_all_empty x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_id -/
theorem correct___eo_prog_str_replace_all_id (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_all_id x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_self -/
theorem correct___eo_prog_str_replace_all_self (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_all_self x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_none -/
theorem correct___eo_prog_str_replace_re_none (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_re_none x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_all_none -/
theorem correct___eo_prog_str_replace_re_all_none (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_re_all_none x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_concat_rec -/
theorem correct___eo_prog_str_len_concat_rec (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_len_concat_rec x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_eq_zero_concat_rec -/
theorem correct___eo_prog_str_len_eq_zero_concat_rec (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_len_eq_zero_concat_rec x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_eq_zero_base -/
theorem correct___eo_prog_str_len_eq_zero_base (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_len_eq_zero_base x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_self -/
theorem correct___eo_prog_str_indexof_self (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_indexof_self x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_no_contains -/
theorem correct___eo_prog_str_indexof_no_contains (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_no_contains x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_oob -/
theorem correct___eo_prog_str_indexof_oob (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_oob x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_oob2 -/
theorem correct___eo_prog_str_indexof_oob2 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_oob2 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_contains_pre -/
theorem correct___eo_prog_str_indexof_contains_pre (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_contains_pre x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_contains_concat_pre -/
theorem correct___eo_prog_str_indexof_contains_concat_pre (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_indexof_contains_concat_pre x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_find_emp -/
theorem correct___eo_prog_str_indexof_find_emp (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_find_emp x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_eq_irr -/
theorem correct___eo_prog_str_indexof_eq_irr (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_eq_irr x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_none -/
theorem correct___eo_prog_str_indexof_re_none (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_indexof_re_none x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_emp_re -/
theorem correct___eo_prog_str_indexof_re_emp_re (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_indexof_re_emp_re x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_concat -/
theorem correct___eo_prog_str_to_lower_concat (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_lower_concat x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_concat -/
theorem correct___eo_prog_str_to_upper_concat (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_upper_concat x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_upper -/
theorem correct___eo_prog_str_to_lower_upper (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_lower_upper x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_lower -/
theorem correct___eo_prog_str_to_upper_lower (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_upper_lower x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_len -/
theorem correct___eo_prog_str_to_lower_len (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_lower_len x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_len -/
theorem correct___eo_prog_str_to_upper_len (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_upper_len x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_from_int -/
theorem correct___eo_prog_str_to_lower_from_int (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_lower_from_int x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_from_int -/
theorem correct___eo_prog_str_to_upper_from_int (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_to_upper_from_int x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_int_concat_neg_one -/
theorem correct___eo_prog_str_to_int_concat_neg_one (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_to_int_concat_neg_one x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_is_digit_elim -/
theorem correct___eo_prog_str_is_digit_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_is_digit_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_empty -/
theorem correct___eo_prog_str_leq_empty (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_leq_empty x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_empty_eq -/
theorem correct___eo_prog_str_leq_empty_eq (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_leq_empty_eq x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_false -/
theorem correct___eo_prog_str_leq_concat_false (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_leq_concat_false x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_true -/
theorem correct___eo_prog_str_leq_concat_true (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (eo_interprets x8 true) ->
  (Not (eo_interprets (__eo_prog_str_leq_concat_true x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_base_1 -/
theorem correct___eo_prog_str_leq_concat_base_1 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_leq_concat_base_1 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_base_2 -/
theorem correct___eo_prog_str_leq_concat_base_2 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_leq_concat_base_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_lt_elim -/
theorem correct___eo_prog_str_lt_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_lt_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_from_int_no_ctn_nondigit -/
theorem correct___eo_prog_str_from_int_no_ctn_nondigit (x1 x2 x3 x4 : Term) :
  (eo_interprets x3 true) ->
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_from_int_no_ctn_nondigit x1 x2 (Proof.pf x3) (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_ctn_contra -/
theorem correct___eo_prog_str_substr_ctn_contra (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_ctn_contra x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_ctn -/
theorem correct___eo_prog_str_substr_ctn (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_substr_ctn x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_dual_ctn -/
theorem correct___eo_prog_str_replace_dual_ctn (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_dual_ctn x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_dual_ctn_false -/
theorem correct___eo_prog_str_replace_dual_ctn_false (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_dual_ctn_false x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_self_ctn_simp -/
theorem correct___eo_prog_str_replace_self_ctn_simp (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_replace_self_ctn_simp x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_emp_ctn_src -/
theorem correct___eo_prog_str_replace_emp_ctn_src (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_replace_emp_ctn_src x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_char_start_eq_len -/
theorem correct___eo_prog_str_substr_char_start_eq_len (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_char_start_eq_len x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_char -/
theorem correct___eo_prog_str_contains_repl_char (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_repl_char x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_self_tgt_char -/
theorem correct___eo_prog_str_contains_repl_self_tgt_char (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_contains_repl_self_tgt_char x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_self -/
theorem correct___eo_prog_str_contains_repl_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_contains_repl_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_tgt -/
theorem correct___eo_prog_str_contains_repl_tgt (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_contains_repl_tgt x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_len_id -/
theorem correct___eo_prog_str_repl_repl_len_id (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_len_id x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_tgt_no_ctn -/
theorem correct___eo_prog_str_repl_repl_src_tgt_no_ctn (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_src_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_tgt_self -/
theorem correct___eo_prog_str_repl_repl_tgt_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_repl_repl_tgt_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_tgt_no_ctn -/
theorem correct___eo_prog_str_repl_repl_tgt_no_ctn (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_self -/
theorem correct___eo_prog_str_repl_repl_src_self (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_str_repl_repl_src_self x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn1 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn1 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_src_inv_no_ctn1 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn2 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn2 (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_src_inv_no_ctn2 x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn3 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn3 (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets x6 true) ->
  (eo_interprets x7 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_src_inv_no_ctn3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_self -/
theorem correct___eo_prog_str_repl_repl_dual_self (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_repl_repl_dual_self x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_ite1 -/
theorem correct___eo_prog_str_repl_repl_dual_ite1 (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_dual_ite1 x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_ite2 -/
theorem correct___eo_prog_str_repl_repl_dual_ite2 (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_dual_ite2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_lookahead_id_simp -/
theorem correct___eo_prog_str_repl_repl_lookahead_id_simp (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_repl_repl_lookahead_id_simp x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_all_elim -/
theorem correct___eo_prog_re_all_elim   (Not (eo_interprets __eo_prog_re_all_elim false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_opt_elim -/
theorem correct___eo_prog_re_opt_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_opt_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_diff_elim -/
theorem correct___eo_prog_re_diff_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_diff_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_plus_elim -/
theorem correct___eo_prog_re_plus_elim (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_plus_elim x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_repeat_elim -/
theorem correct___eo_prog_re_repeat_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_repeat_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_swap -/
theorem correct___eo_prog_re_concat_star_swap (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_re_concat_star_swap x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_repeat -/
theorem correct___eo_prog_re_concat_star_repeat (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_re_concat_star_repeat x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_subsume1 -/
theorem correct___eo_prog_re_concat_star_subsume1 (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_re_concat_star_subsume1 x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_subsume2 -/
theorem correct___eo_prog_re_concat_star_subsume2 (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_re_concat_star_subsume2 x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_merge -/
theorem correct___eo_prog_re_concat_merge (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_re_concat_merge x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_all -/
theorem correct___eo_prog_re_union_all (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_union_all x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_const_elim -/
theorem correct___eo_prog_re_union_const_elim (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_re_union_const_elim x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_all -/
theorem correct___eo_prog_re_inter_all (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_inter_all x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_none -/
theorem correct___eo_prog_re_star_none   (Not (eo_interprets __eo_prog_re_star_none false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_emp -/
theorem correct___eo_prog_re_star_emp   (Not (eo_interprets __eo_prog_re_star_emp false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_star -/
theorem correct___eo_prog_re_star_star (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_star_star x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_refl -/
theorem correct___eo_prog_re_range_refl (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_re_range_refl x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_emp -/
theorem correct___eo_prog_re_range_emp (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x3 true) ->
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_re_range_emp x1 x2 (Proof.pf x3) (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_non_singleton_1 -/
theorem correct___eo_prog_re_range_non_singleton_1 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_re_range_non_singleton_1 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_non_singleton_2 -/
theorem correct___eo_prog_re_range_non_singleton_2 (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_re_range_non_singleton_2 x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_union_char -/
theorem correct___eo_prog_re_star_union_char (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_star_union_char x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_union_drop_emp -/
theorem correct___eo_prog_re_star_union_drop_emp (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_star_union_drop_emp x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_loop_neg -/
theorem correct___eo_prog_re_loop_neg (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_re_loop_neg x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_cstring -/
theorem correct___eo_prog_re_inter_cstring (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_re_inter_cstring x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_cstring_neg -/
theorem correct___eo_prog_re_inter_cstring_neg (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_re_inter_cstring_neg x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_include -/
theorem correct___eo_prog_str_substr_len_include (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_len_include x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_include_pre -/
theorem correct___eo_prog_str_substr_len_include_pre (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_len_include_pre x1 x2 x3 x4 (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_norm -/
theorem correct___eo_prog_str_substr_len_norm (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_substr_len_norm x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_len_rev -/
theorem correct___eo_prog_seq_len_rev (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_len_rev x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_rev -/
theorem correct___eo_prog_seq_rev_rev (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_rev_rev x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_concat -/
theorem correct___eo_prog_seq_rev_concat (x1 x2 x3 : Term) :
  (Not (eo_interprets (__eo_prog_seq_rev_concat x1 x2 x3) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_self_emp -/
theorem correct___eo_prog_str_eq_repl_self_emp (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_self_emp x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_no_change -/
theorem correct___eo_prog_str_eq_repl_no_change (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_no_change x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_tgt_eq_len -/
theorem correct___eo_prog_str_eq_repl_tgt_eq_len (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_tgt_eq_len x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_len_one_emp_prefix -/
theorem correct___eo_prog_str_eq_repl_len_one_emp_prefix (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_len_one_emp_prefix x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_emp_tgt_nemp -/
theorem correct___eo_prog_str_eq_repl_emp_tgt_nemp (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_emp_tgt_nemp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_nemp_src_emp -/
theorem correct___eo_prog_str_eq_repl_nemp_src_emp (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets x5 true) ->
  (eo_interprets x6 true) ->
  (Not (eo_interprets (__eo_prog_str_eq_repl_nemp_src_emp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_self_src -/
theorem correct___eo_prog_str_eq_repl_self_src (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_eq_repl_self_src x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_len_unit -/
theorem correct___eo_prog_seq_len_unit (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_len_unit x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_nth_unit -/
theorem correct___eo_prog_seq_nth_unit (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_nth_unit x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_unit -/
theorem correct___eo_prog_seq_rev_unit (x1 : Term) :
  (Not (eo_interprets (__eo_prog_seq_rev_unit x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_empty -/
theorem correct___eo_prog_re_in_empty (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_in_empty x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_sigma -/
theorem correct___eo_prog_re_in_sigma (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_in_sigma x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_sigma_star -/
theorem correct___eo_prog_re_in_sigma_star (x1 : Term) :
  (Not (eo_interprets (__eo_prog_re_in_sigma_star x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_cstring -/
theorem correct___eo_prog_re_in_cstring (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_in_cstring x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_comp -/
theorem correct___eo_prog_re_in_comp (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_re_in_comp x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_union_elim -/
theorem correct___eo_prog_str_in_re_union_elim (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_union_elim x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_inter_elim -/
theorem correct___eo_prog_str_in_re_inter_elim (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_inter_elim x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_range_elim -/
theorem correct___eo_prog_str_in_re_range_elim (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_str_in_re_range_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_contains -/
theorem correct___eo_prog_str_in_re_contains (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_contains x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_from_int_nemp_dig_range -/
theorem correct___eo_prog_str_in_re_from_int_nemp_dig_range (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_str_in_re_from_int_nemp_dig_range x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_from_int_dig_range -/
theorem correct___eo_prog_str_in_re_from_int_dig_range (x1 : Term) :
  (Not (eo_interprets (__eo_prog_str_in_re_from_int_dig_range x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_refl -/
theorem correct___eo_prog_eq_refl (x1 : Term) :
  (Not (eo_interprets (__eo_prog_eq_refl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_symm -/
theorem correct___eo_prog_eq_symm (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_eq_symm x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_cond_deq -/
theorem correct___eo_prog_eq_cond_deq (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_eq_cond_deq x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_ite_lift -/
theorem correct___eo_prog_eq_ite_lift (x1 x2 x3 x4 : Term) :
  (Not (eo_interprets (__eo_prog_eq_ite_lift x1 x2 x3 x4) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_binary_elim -/
theorem correct___eo_prog_distinct_binary_elim (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_binary_elim x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv -/
theorem correct___eo_prog_uf_bv2nat_int2bv (x1 x2 x3 : Term) :
  (eo_interprets x3 true) ->
  (Not (eo_interprets (__eo_prog_uf_bv2nat_int2bv x1 x2 (Proof.pf x3)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv_extend -/
theorem correct___eo_prog_uf_bv2nat_int2bv_extend (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_uf_bv2nat_int2bv_extend x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv_extract -/
theorem correct___eo_prog_uf_bv2nat_int2bv_extract (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_uf_bv2nat_int2bv_extract x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bv2nat -/
theorem correct___eo_prog_uf_int2bv_bv2nat (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_uf_int2bv_bv2nat x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_geq_elim -/
theorem correct___eo_prog_uf_bv2nat_geq_elim (x1 x2 x3 x4 : Term) :
  (eo_interprets x4 true) ->
  (Not (eo_interprets (__eo_prog_uf_bv2nat_geq_elim x1 x2 x3 (Proof.pf x4)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bvult_equiv -/
theorem correct___eo_prog_uf_int2bv_bvult_equiv (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_uf_int2bv_bvult_equiv x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bvule_equiv -/
theorem correct___eo_prog_uf_int2bv_bvule_equiv (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_uf_int2bv_bvule_equiv x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_sbv_to_int_elim -/
theorem correct___eo_prog_uf_sbv_to_int_elim (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets x4 true) ->
  (eo_interprets x5 true) ->
  (Not (eo_interprets (__eo_prog_uf_sbv_to_int_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_evaluate -/
theorem correct___eo_prog_evaluate (x1 : Term) :
  (Not (eo_interprets (__eo_prog_evaluate x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_values -/
theorem correct___eo_prog_distinct_values (x1 x2 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_values x1 x2) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_aci_norm -/
theorem correct___eo_prog_aci_norm (x1 : Term) :
  (Not (eo_interprets (__eo_prog_aci_norm x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_absorb -/
theorem correct___eo_prog_absorb (x1 : Term) :
  (Not (eo_interprets (__eo_prog_absorb x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_card_conflict -/
theorem correct___eo_prog_distinct_card_conflict (x1 : Term) :
  (Not (eo_interprets (__eo_prog_distinct_card_conflict x1) false)) :=
by
  sorry



/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (eo_interprets F false) :=
by
  sorry

/- ---------------------------------------------- -/

