import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smt_eval_to_real_idem (v : SmtValue) :
    __smtx_model_eval_to_real (__smtx_model_eval_to_real v) =
      __smtx_model_eval_to_real v := by
  cases v <;> rfl

private theorem smt_qdiv_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       let yr := __smtx_model_eval_to_real yv
       let xr := __smtx_model_eval_to_real xv
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yr (SmtValue.Rational (native_mk_rational 0 1)))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_qdiv_by_zero_id
             (SmtType.FunType SmtType.Real SmtType.Real))
           xr)
         (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [__smtx_model_eval.eq_128]

private theorem smt_qdiv_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       let yr := __smtx_model_eval_to_real yv
       let xr := __smtx_model_eval_to_real xv
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yr (SmtValue.Rational (native_mk_rational 0 1)))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_qdiv_by_zero_id
             (SmtType.FunType SmtType.Real SmtType.Real))
           xr)
         (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [smt_qdiv_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_qdiv_eval_reduction_normalized_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq
            (SmtTerm.to_real y)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv
            (SmtTerm.to_real x)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total (SmtTerm.to_real x) (SmtTerm.to_real y)))) := by
  rw [smt_qdiv_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_19,
    __smtx_model_eval.eq_3, __smtx_model_eval.eq_128,
    __smtx_model_eval.eq_129]
  rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_3]
  rw [__smtx_model_eval.eq_19]
  rw [smt_eval_to_real_idem (__smtx_model_eval M x)]
  simp [__smtx_model_eval_to_real, __smtx_model_eval_ite, __smtx_model_eval_eq,
    native_veq]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_div_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.div x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [__smtx_model_eval.eq_24]

private theorem smt_div_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [smt_div_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_div_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.div x (SmtTerm.Numeral 0))
          (SmtTerm.div_total x y))) := by
  rw [smt_div_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_24, __smtx_model_eval.eq_30]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_div_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Numeral n =>
    by_cases hZero : n = 0 <;>
      simp [__smtx_model_eval.eq_2, hZero] <;>
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_mod_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_mod_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_mod_total xv yv)) := by
  rw [__smtx_model_eval.eq_25]

private theorem smt_mod_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_mod_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_mod_total xv yv)) := by
  rw [smt_mod_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_mod_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.mod x (SmtTerm.Numeral 0))
          (SmtTerm.mod_total x y))) := by
  rw [smt_mod_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_25, __smtx_model_eval.eq_31]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_mod_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Numeral n =>
    by_cases hZero : n = 0 <;>
      simp [__smtx_model_eval.eq_2, hZero] <;>
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_abs_eval_reduction_self
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.abs x) =
      (let xv := __smtx_model_eval M x
       let zero := SmtValue.Numeral 0
       __smtx_model_eval_ite
         (__smtx_model_eval_lt xv zero)
         (__smtx_model_eval__ zero xv)
         xv) := by
  rw [__smtx_model_eval.eq_22]
  rfl

private theorem smt_abs_eval_reduction_rel
    (M : SmtModel) (x : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (let xv := __smtx_model_eval M x
       let zero := SmtValue.Numeral 0
       __smtx_model_eval_ite
         (__smtx_model_eval_lt xv zero)
         (__smtx_model_eval__ zero xv)
         xv) := by
  rw [smt_abs_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_abs_eval_reduction_term_rel
    (M : SmtModel) (x : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt x (SmtTerm.Numeral 0))
          (SmtTerm.uneg x)
          x)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [smt_abs_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_15, __smtx_model_eval.eq_2, __smtx_model_eval.eq_23]
  cases hx : __smtx_model_eval M x <;>
    simp [__smtx_model_eval_lt, __smtx_model_eval_ite, __smtx_model_eval__,
      __smtx_model_eval_uneg, __smtx_model_eval_eq, native_veq,
      native_zplus, native_zneg, native_zlt]
  case Numeral n =>
    by_cases hlt : n < 0 <;>
      simp [hlt]

theorem cmd_step_arith_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_reduction args premises) :=
by
  sorry
