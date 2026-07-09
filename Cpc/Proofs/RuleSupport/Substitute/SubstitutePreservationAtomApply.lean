import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomGeneric

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

theorem false_of_apply_stuck_has_smt_translation
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply Term.Stuck a)) :
    False := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) ≠
      SmtType.None at hTrans
  exact hTrans (TranslationProofs.typeof_apply_none_eq (__eo_to_smt a))

theorem false_of_apply_uop1_seq_empty_has_smt_translation
    (idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.seq_empty idx) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.seq_empty idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_seq_empty hTransEo

theorem false_of_apply_uop1_set_empty_has_smt_translation
    (idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.set_empty idx) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.set_empty idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_set_empty hTransEo

theorem false_of_apply_uop1_update_has_smt_translation
    (idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.update idx) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.update idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_uop1_translate_apply_none hTransEo rfl

theorem false_of_apply_uop1_tuple_update_has_smt_translation
    (idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_uop1_translate_apply_none hTransEo rfl

theorem false_of_apply_uop2_at_bv_has_smt_translation
    (i j a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 UserOp2._at_bv i j) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp2 UserOp2._at_bv i j) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_at_bv hTransEo

theorem false_of_apply_uop2_at_const_has_smt_translation
    (i j a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 UserOp2._at_const i j) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp2 UserOp2._at_const i j) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_uop2_translate_apply_none hTransEo rfl

private theorem eo_to_smt_quant_skolemize_ne_dt_sel
    (vs : Term) (G : SmtTerm) (n : native_Nat) :
    ∀ s d i j,
      __eo_to_smt_quantifiers_skolemize vs G n ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem eo_to_smt_quant_skolemize_ne_dt_tester
    (vs : Term) (G : SmtTerm) (n : native_Nat) :
    ∀ s d i,
      __eo_to_smt_quantifiers_skolemize vs G n ≠
        SmtTerm.DtTester s d i := by
  intro s d i
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

private theorem eo_to_smt_quant_skolemize_top_ne_dt_sel
    (q idx : Term) :
    ∀ s d i j,
      __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
            native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_sel
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i j h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_tester
    (q idx : Term) :
    ∀ s d i,
      __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
            native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_tester
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i h

theorem substitute_simul_apply_quant_skolemize_preserves_type_and_translation_of_typeof_ne_stuck
    (q idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply
              (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) a)
            xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) a)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx) a)
          xs ts bvs) := by
  exact
    substitute_simul_apply_atom_generic_preserves_type_and_translation_of_typeof_ne_stuck
      (Term.UOp2 UserOp2._at_quantifiers_skolemize q idx)
      a xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes
      (by intro f x h; cases h)
      (by intro name U h; cases h)
      (by intro h; cases h)
      (by intro q' v vs h; cases h)
      (by rfl)
      (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx)
      (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx)
      hTrans hARec hTy

theorem false_of_apply_uop3_re_unfold_pos_component_has_smt_translation
    (str re idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.UOp3 UserOp3._at_re_unfold_pos_component str re idx) a)) :
    False := by
  have hTransEo :
      eoHasSmtTranslation
        (Term.Apply
          (Term.UOp3 UserOp3._at_re_unfold_pos_component str re idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  exact false_of_apply_re_unfold_pos_component hTransEo

private theorem eo_to_smt_witness_string_length_ne_dt_sel
    (T len id : Term) :
    ∀ s d i j,
      __eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length T len id) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  change
    native_ite (__eo_to_smt_nat_is_valid len)
      (native_ite (__eo_to_smt_nat_is_valid id)
        (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
            (__eo_to_smt len)))
        SmtTerm.None)
      SmtTerm.None =
      SmtTerm.DtSel s d i j at h
  unfold native_ite at h
  split at h <;> try cases h
  split at h <;> cases h

private theorem eo_to_smt_witness_string_length_ne_dt_tester
    (T len id : Term) :
    ∀ s d i,
      __eo_to_smt
          (Term.UOp3 UserOp3._at_witness_string_length T len id) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  change
    native_ite (__eo_to_smt_nat_is_valid len)
      (native_ite (__eo_to_smt_nat_is_valid id)
        (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
            (__eo_to_smt len)))
        SmtTerm.None)
      SmtTerm.None =
      SmtTerm.DtTester s d i at h
  unfold native_ite at h
  split at h <;> try cases h
  split at h <;> cases h

theorem substitute_simul_apply_witness_string_length_preserves_type_and_translation_of_typeof_ne_stuck
    (T len id a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp3 UserOp3._at_witness_string_length T len id) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp3 UserOp3._at_witness_string_length T len id)
              a)
            xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp3 UserOp3._at_witness_string_length T len id) a)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.UOp3 UserOp3._at_witness_string_length T len id) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp3 UserOp3._at_witness_string_length T len id) a)
          xs ts bvs) := by
  exact
    substitute_simul_apply_atom_generic_preserves_type_and_translation_of_typeof_ne_stuck
      (Term.UOp3 UserOp3._at_witness_string_length T len id)
      a xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes
      (by intro f x h; cases h)
      (by intro name U h; cases h)
      (by intro h; cases h)
      (by intro q v vs h; cases h)
      (by rfl)
      (eo_to_smt_witness_string_length_ne_dt_sel T len id)
      (eo_to_smt_witness_string_length_ne_dt_tester T len id)
      hTrans hARec hTy

end SubstitutePreservationSupport
