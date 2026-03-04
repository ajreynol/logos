import Cpc.Logos

open Eo

#eval!
let x := (Term.UConst 1 Term.Int);
let y := (Term.UConst 2 Term.Int);
(__eo_checker_is_refutation
(Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq y) x))
(Term.Apply (Term.Apply Term.and (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)))
(Term.Boolean true)))
(CCmdList.cons (CCmd.symm (Term.Numeral 0))
(CCmdList.cons (CCmd.contra (Term.Numeral 2) (Term.Numeral 0))
CCmdList.nil))
)
