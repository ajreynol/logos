import Cpc.Logos

#eval!
let t1 := (Eo.Term.USort 1);
let t2 := (Eo.Term.UConst 1 t1);
let t3 := (Eo.Term.UConst 2 t1);
let t4 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.eq t3) t2);
let t5 := (Eo.Term.UConst 3 t1);
let t6 := (Eo.Term.UConst 4 t1);
let t7 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.eq t6) t5);
let t8 := (Eo.Term.UConst 5 Eo.Term.Bool);
let t9 := (Eo.Term.UConst 6 Eo.Term.Bool);
let t10 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.UConst 7 Eo.Term.Bool)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t9) (Eo.Term.Boolean true)));
let t11 := (Eo.Term.UConst 8 (Eo.Term.Apply (Eo.Term.Apply Eo.Term.FunType t1) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.FunType t1) t1)));
let t12 := (Eo.Term.Apply (Eo.Term.Apply t11 t3) t6);
let t13 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.eq t12) (Eo.Term.Apply (Eo.Term.Apply t11 t2) t5));
let t14 := (Eo.Term.Apply Eo.Term.not t13);
let t15 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons (Eo.Term.Boolean false)) Eo.Term.__eo_List_nil);
let t16 := (Eo.Term.Apply Eo.Term.not t10);
let t17 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t9) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t16) (Eo.Term.Boolean false)));
let t18 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t4) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t7) (Eo.Term.Boolean true)));
let t19 := (Eo.Term.Apply Eo.Term.not t7);
let t20 := (Eo.Term.Apply Eo.Term.not t4);
let t21 := (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t13) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t20) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t19) (Eo.Term.Boolean false))));
(Eo.__eo_checker_is_refutation
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t4)
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t7)
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and t8) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Boolean true)) (Eo.Term.Boolean true))))
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or (Eo.Term.Apply Eo.Term.not t8)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t10) (Eo.Term.Boolean false))))
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or (Eo.Term.Apply Eo.Term.not t9)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t14) (Eo.Term.Boolean false))))
(Eo.Term.Boolean true))))))
(Eo.CCmdList.cons (Eo.CCmd.and_elim (Eo.Term.Numeral 0) (Eo.Term.Numeral 2))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t8)
(Eo.CCmdList.cons (Eo.CCmd.chain_m_resolution t10 t15 (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t8) Eo.Term.__eo_List_nil) (Eo.CIndexList.cons (Eo.Term.Numeral 2) (Eo.CIndexList.cons (Eo.Term.Numeral 0) Eo.CIndexList.nil)))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t10)
(Eo.CCmdList.cons (Eo.CCmd.cnf_and_pos t10 (Eo.Term.Numeral 1))
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t16) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t9) (Eo.Term.Boolean false))))
(Eo.CCmdList.cons (Eo.CCmd.reordering t17 (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t17)
(Eo.CCmdList.cons (Eo.CCmd.chain_m_resolution t9 t15 (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t10) Eo.Term.__eo_List_nil) (Eo.CIndexList.cons (Eo.Term.Numeral 0) (Eo.CIndexList.cons (Eo.Term.Numeral 2) Eo.CIndexList.nil)))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t9)
(Eo.CCmdList.cons (Eo.CCmd.chain_m_resolution t14 t15 (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t9) Eo.Term.__eo_List_nil) (Eo.CIndexList.cons (Eo.Term.Numeral 5) (Eo.CIndexList.cons (Eo.Term.Numeral 0) Eo.CIndexList.nil)))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t14)
(Eo.CCmdList.cons (Eo.CCmd.assume_push t4)
(Eo.CCmdList.cons (Eo.CCmd.assume_push t7)
(Eo.CCmdList.cons (Eo.CCmd.cong t12 (Eo.CIndexList.cons (Eo.Term.Numeral 12) (Eo.CIndexList.cons (Eo.Term.Numeral 11) Eo.CIndexList.nil)))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t13)
(Eo.CCmdList.cons (Eo.CCmd.scope (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.scope (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.process_scope t13 (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Apply (Eo.Term.Apply Eo.Term.imp t18) t13))
(Eo.CCmdList.cons (Eo.CCmd.implies_elim (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or (Eo.Term.Apply Eo.Term.not t18)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t13) (Eo.Term.Boolean false))))
(Eo.CCmdList.cons (Eo.CCmd.cnf_and_neg t18)
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t18) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t20) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t19) (Eo.Term.Boolean false)))))
(Eo.CCmdList.cons (Eo.CCmd.resolution (Eo.Term.Boolean true) t18 (Eo.Term.Numeral 0) (Eo.Term.Numeral 1))
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t20) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t19) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.or t13) (Eo.Term.Boolean false)))))
(Eo.CCmdList.cons (Eo.CCmd.reordering t21 (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.check_proven t21)
(Eo.CCmdList.cons (Eo.CCmd.chain_m_resolution (Eo.Term.Boolean false) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons (Eo.Term.Boolean true)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons (Eo.Term.Boolean false)) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons (Eo.Term.Boolean false)) Eo.Term.__eo_List_nil))) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t13) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t7) (Eo.Term.Apply (Eo.Term.Apply Eo.Term.__eo_List_cons t4) Eo.Term.__eo_List_nil))) (Eo.CIndexList.cons (Eo.Term.Numeral 0) (Eo.CIndexList.cons (Eo.Term.Numeral 6) (Eo.CIndexList.cons (Eo.Term.Numeral 15) (Eo.CIndexList.cons (Eo.Term.Numeral 16) Eo.CIndexList.nil)))))
(Eo.CCmdList.cons (Eo.CCmd.check_proven (Eo.Term.Boolean false))
Eo.CCmdList.nil))))))))))))))))))))))))))))))
)
