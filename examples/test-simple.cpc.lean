import Cpc.Logos

#eval!
let x := (Eo.Term.UConst 1 Eo.Term.Int);
let y := (Eo.Term.UConst 2 Eo.Term.Int);
(Eo.__eo_checker_is_refutation
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Apply (Eo.Term.Apply Eo.Term.eq y) x))
(Eo.Term.Apply (Eo.Term.Apply Eo.Term.and (Eo.Term.Apply Eo.Term.not (Eo.Term.Apply (Eo.Term.Apply Eo.Term.eq x) y)))
(Eo.Term.Boolean true)))
(Eo.CCmdList.cons (Eo.CCmd.symm (Eo.Term.Numeral 0))
(Eo.CCmdList.cons (Eo.CCmd.contra (Eo.Term.Numeral 2) (Eo.Term.Numeral 0))
Eo.CCmdList.nil))
)
