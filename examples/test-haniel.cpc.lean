import Cpc.Logos
open Eo
#eval!
let t1 := (Term.USort 1);
let t2 := (Term.UConst 1 t1);
let t3 := (Term.UConst 2 t1);
let t4 := (Term.Apply (Term.Apply Term.eq t3) t2);
let t5 := (Term.UConst 3 t1);
let t6 := (Term.UConst 4 t1);
let t7 := (Term.Apply (Term.Apply Term.eq t6) t5);
let t8 := (Term.UConst 5 Term.Bool);
let t9 := (Term.UConst 6 Term.Bool);
let t10 := (Term.Apply (Term.Apply Term.and (Term.UConst 7 Term.Bool)) (Term.Apply (Term.Apply Term.and t9) (Term.Boolean true)));
let t11 := (Term.UConst 8 (Term.Apply (Term.Apply Term.FunType t1) (Term.Apply (Term.Apply Term.FunType t1) t1)));
let t12 := (Term.Apply (Term.Apply t11 t3) t6);
let t13 := (Term.Apply (Term.Apply Term.eq t12) (Term.Apply (Term.Apply t11 t2) t5));
let t14 := (Term.Apply Term.not t13);
let t15 := (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Boolean false)) Term.__eo_List_nil);
let t16 := (Term.Apply Term.not t10);
let t17 := (Term.Apply (Term.Apply Term.or t9) (Term.Apply (Term.Apply Term.or t16) (Term.Boolean false)));
let t18 := (Term.Apply (Term.Apply Term.and t4) (Term.Apply (Term.Apply Term.and t7) (Term.Boolean true)));
let t19 := (Term.Apply Term.not t7);
let t20 := (Term.Apply Term.not t4);
let t21 := (Term.Apply (Term.Apply Term.or t13) (Term.Apply (Term.Apply Term.or t20) (Term.Apply (Term.Apply Term.or t19) (Term.Boolean false))));
(__eo_checker_is_refutation
(Term.Apply (Term.Apply Term.and t4)
(Term.Apply (Term.Apply Term.and t7)
(Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.and t8) (Term.Apply (Term.Apply Term.and (Term.Boolean true)) (Term.Boolean true))))
(Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t8)) (Term.Apply (Term.Apply Term.or t10) (Term.Boolean false))))
(Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t9)) (Term.Apply (Term.Apply Term.or t14) (Term.Boolean false))))
(Term.Boolean true))))))
(CCmdList.cons (CCmd.and_elim (Term.Numeral 0) 2)
(CCmdList.cons (CCmd.check_proven t8)
(CCmdList.cons (CCmd.chain_m_resolution t10 t15 (Term.Apply (Term.Apply Term.__eo_List_cons t8) Term.__eo_List_nil) (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil)))
(CCmdList.cons (CCmd.check_proven t10)
(CCmdList.cons (CCmd.cnf_and_pos t10 (Term.Numeral 1))
(CCmdList.cons (CCmd.check_proven (Term.Apply (Term.Apply Term.or t16) (Term.Apply (Term.Apply Term.or t9) (Term.Boolean false))))
(CCmdList.cons (CCmd.reordering t17 0)
(CCmdList.cons (CCmd.check_proven t17)
(CCmdList.cons (CCmd.chain_m_resolution t9 t15 (Term.Apply (Term.Apply Term.__eo_List_cons t10) Term.__eo_List_nil) (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil)))
(CCmdList.cons (CCmd.check_proven t9)
(CCmdList.cons (CCmd.chain_m_resolution t14 t15 (Term.Apply (Term.Apply Term.__eo_List_cons t9) Term.__eo_List_nil) (CIndexList.cons 5 (CIndexList.cons 0 CIndexList.nil)))
(CCmdList.cons (CCmd.check_proven t14)
(CCmdList.cons (CCmd.assume_push t4)
(CCmdList.cons (CCmd.assume_push t7)
(CCmdList.cons (CCmd.cong t12 (CIndexList.cons 12 (CIndexList.cons 11 CIndexList.nil)))
(CCmdList.cons (CCmd.check_proven t13)
(CCmdList.cons (CCmd.scope 0)
(CCmdList.cons (CCmd.scope 0)
(CCmdList.cons (CCmd.process_scope t13 0)
(CCmdList.cons (CCmd.check_proven (Term.Apply (Term.Apply Term.imp t18) t13))
(CCmdList.cons (CCmd.implies_elim 0)
(CCmdList.cons (CCmd.check_proven (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t18)) (Term.Apply (Term.Apply Term.or t13) (Term.Boolean false))))
(CCmdList.cons (CCmd.cnf_and_neg t18)
(CCmdList.cons (CCmd.check_proven (Term.Apply (Term.Apply Term.or t18) (Term.Apply (Term.Apply Term.or t20) (Term.Apply (Term.Apply Term.or t19) (Term.Boolean false)))))
(CCmdList.cons (CCmd.resolution (Term.Boolean true) t18 0 1)
(CCmdList.cons (CCmd.check_proven (Term.Apply (Term.Apply Term.or t20) (Term.Apply (Term.Apply Term.or t19) (Term.Apply (Term.Apply Term.or t13) (Term.Boolean false)))))
(CCmdList.cons (CCmd.reordering t21 0)
(CCmdList.cons (CCmd.check_proven t21)
(CCmdList.cons (CCmd.chain_m_resolution (Term.Boolean false) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Boolean true)) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Boolean false)) (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Boolean false)) Term.__eo_List_nil))) (Term.Apply (Term.Apply Term.__eo_List_cons t13) (Term.Apply (Term.Apply Term.__eo_List_cons t7) (Term.Apply (Term.Apply Term.__eo_List_cons t4) Term.__eo_List_nil))) (CIndexList.cons 0 (CIndexList.cons 6 (CIndexList.cons 15 (CIndexList.cons 16 CIndexList.nil)))))
(CCmdList.cons (CCmd.check_proven (Term.Boolean false))
CCmdList.nil))))))))))))))))))))))))))))))
)
