import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Builds the right-associated conjunction of a list of premise terms, using `true` as the empty case. -/
def premiseAndFormulaList : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply (Term.UOp UserOp.and) p) (premiseAndFormulaList ps)

/-- Collects the proven terms referenced by a premise index list in a checker state. -/
def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

/-- Predicate asserting that every term in a list is interpreted as `true` by a model. -/
def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

/--
Two models agree on the global part of the interpretation.

Variables may vary, but user constants and native function interpretations are
kept fixed. This is the model relation used when a binder pushes fresh variable
assignments.
-/
def model_agrees_on_globals (M N : SmtModel) : Prop :=
  (∀ s T, native_model_lookup M s T = native_model_lookup N s T) ∧
  (∀ fid T U, native_model_fun_lookup M fid T U =
    native_model_fun_lookup N fid T U)

abbrev SmtVarKey : Type := native_String × SmtType

/-- Agreement on the currently bound SMT variables. -/
def model_agrees_on_vars (vars : List SmtVarKey) (M N : SmtModel) : Prop :=
  ∀ s T, (s, T) ∈ vars ->
    native_model_var_lookup M s T = native_model_var_lookup N s T

/-- Agreement on globals plus a finite bound-variable environment. -/
structure model_agrees_on_env (vars : List SmtVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq : model_agrees_on_vars vars M N

theorem model_agrees_on_globals_refl (M : SmtModel) :
  model_agrees_on_globals M M :=
by
  exact ⟨by intro s T; rfl, by intro fid T U; rfl⟩

theorem model_agrees_on_env_refl (vars : List SmtVarKey) (M : SmtModel) :
  model_agrees_on_env vars M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T hMem; rfl⟩

theorem model_agrees_on_globals_trans {M N K : SmtModel} :
  model_agrees_on_globals M N ->
  model_agrees_on_globals N K ->
  model_agrees_on_globals M K :=
by
  intro hMN hNK
  exact
    ⟨by
      intro s T
      exact (hMN.1 s T).trans (hNK.1 s T),
    by
      intro fid T U
      exact (hMN.2 fid T U).trans (hNK.2 fid T U)⟩

theorem model_agrees_on_globals_push
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
  model_agrees_on_globals M (native_model_push M s T v) :=
by
  exact
    ⟨by
      intro s' T'
      simp [native_model_lookup, native_model_key, native_model_push],
    by
      intro fid A B
      simp [native_model_fun_lookup, native_model_key, native_model_push]⟩

theorem model_agrees_on_globals_push₂
    {M N : SmtModel} {s : native_String} {T : SmtType} {v : SmtValue} :
  model_agrees_on_globals M N ->
  model_agrees_on_globals (native_model_push M s T v) (native_model_push N s T v) :=
by
  intro hAgree
  exact
    ⟨by
      intro s' T'
      simpa [native_model_lookup, native_model_key, native_model_push]
        using hAgree.1 s' T',
    by
      intro fid A B
      simpa [native_model_fun_lookup, native_model_key, native_model_push]
        using hAgree.2 fid A B⟩

theorem model_agrees_on_env_push_same
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue} :
  model_agrees_on_env vars M N ->
  model_agrees_on_env ((s, T) :: vars)
    (native_model_push M s T v) (native_model_push N s T v) :=
by
  intro hAgree
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hMem
  cases hMem with
  | head =>
      simp [native_model_var_lookup, native_model_push]
  | tail _ hTail =>
      by_cases hKey :
          ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
            { isVar := true, name := s, ty := T }
      · cases hKey
        simp [native_model_var_lookup, native_model_push]
      · simpa [native_model_var_lookup, native_model_push, hKey]
          using hAgree.vars_eq s' T' hTail

theorem native_eval_ifun_apply_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (fid : native_String) (T U : SmtType) (i : SmtValue) :
  native_eval_ifun_apply M fid T U i =
    native_eval_ifun_apply N fid T U i :=
by
  by_cases hDefault : fid = native_default_ifun_id
  · simp [native_eval_ifun_apply, hDefault]
  · simp [native_eval_ifun_apply, hDefault, hAgree.2 fid T U]

theorem smtx_model_eval_apply_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (f i : SmtValue) :
  __smtx_model_eval_apply M f i =
    __smtx_model_eval_apply N f i :=
by
  cases f <;> cases i <;>
    simp [__smtx_model_eval_apply, native_eval_ifun_apply_eq_of_globals hAgree]

theorem smtx_seq_nth_wrong_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (s : SmtSeq) (n : native_Int) (T : SmtType) :
  __smtx_seq_nth_wrong M s n T =
    __smtx_seq_nth_wrong N s n T :=
by
  cases T <;> simp [__smtx_seq_nth_wrong, hAgree.1]

theorem smtx_seq_nth_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (v n : SmtValue) :
  __smtx_seq_nth M v n =
    __smtx_seq_nth N v n :=
by
  cases v <;> cases n <;>
    simp [__smtx_seq_nth, smtx_seq_nth_wrong_eq_of_globals hAgree]

theorem smtx_model_eval_dt_sel_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (s : native_String) (d : SmtDatatype) (n m : native_Nat) (v : SmtValue) :
  __smtx_model_eval_dt_sel M s d n m v =
    __smtx_model_eval_dt_sel N s d n m v :=
by
  cases v <;>
    simp [__smtx_model_eval_dt_sel, smtx_model_eval_apply_eq_of_globals hAgree,
      hAgree.1 (native_wrong_apply_sel_id n m)
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m))]

theorem native_eval_texists_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  native_eval_texists M s T body = native_eval_texists N s T body :=
by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v] using hEval⟩
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

theorem native_eval_tforall_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  native_eval_tforall M s T body = native_eval_tforall N s T body :=
by
  classical
  let PM : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PN : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h v hTy hCanon
      simpa [hBody v] using h v hTy hCanon
    · intro h v hTy hCanon
      simpa [← hBody v] using h v hTy hCanon
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

theorem native_eval_tchoice_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  native_eval_tchoice M s T body = native_eval_tchoice N s T body :=
by
  classical
  let PredM : SmtValue -> Prop := fun v =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PredN : SmtValue -> Prop := fun v =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  let PTy : Prop :=
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical_bool v
  change
    (if hSat : ∃ v : SmtValue, PredM v then Classical.choose hSat
      else if hTy : PTy then Classical.choose hTy else SmtValue.NotValue) =
    (if hSat : ∃ v : SmtValue, PredN v then Classical.choose hSat
      else if hTy : PTy then Classical.choose hTy else SmtValue.NotValue)
  have hPredEq : PredM = PredN := by
    funext v
    apply propext
    constructor
    · intro h
      exact ⟨h.1, h.2.1, by simpa [hBody v] using h.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, by simpa [← hBody v] using h.2.2⟩
  rw [hPredEq]

noncomputable section ChoiceNthAux

def nativeEvalTChoiceNthAux
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
    native_Nat -> SmtValue
  | native_nat_zero =>
      native_eval_tchoice M s T body
  | native_nat_succ n =>
      let v := native_eval_tchoice M s T body
      match body with
      | SmtTerm.exists s' T' body' =>
          nativeEvalTChoiceNthAux (native_model_push M s T v) s' T' body' n
      | _ => SmtValue.NotValue

theorem native_eval_tchoice_nth_eq_aux
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body : SmtTerm) (n : native_Nat) :
  native_eval_tchoice_nth M s T body n =
    nativeEvalTChoiceNthAux M s T body n :=
by
  rfl

end ChoiceNthAux

/-- SMT term closedness relative to a stack of bound variables. -/
def SmtTermClosedIn (vars : List SmtVarKey) : SmtTerm -> Prop
  | SmtTerm.None => True
  | SmtTerm.Boolean _ => True
  | SmtTerm.Numeral _ => True
  | SmtTerm.Rational _ => True
  | SmtTerm.String _ => True
  | SmtTerm.Binary _ _ => True
  | SmtTerm.Apply f x => SmtTermClosedIn vars f ∧ SmtTermClosedIn vars x
  | SmtTerm.Var s T => (s, T) ∈ vars
  | SmtTerm.ite c t e =>
      SmtTermClosedIn vars c ∧ SmtTermClosedIn vars t ∧ SmtTermClosedIn vars e
  | SmtTerm.eq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.exists s T body => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.forall s T body => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.choice_nth s T body _ => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.map_diff x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.DtCons _ _ _ => True
  | SmtTerm.DtSel _ _ _ _ => True
  | SmtTerm.DtTester _ _ _ => True
  | SmtTerm.UConst _ _ => True
  | SmtTerm.not x => SmtTermClosedIn vars x
  | SmtTerm.or x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.and x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.imp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.xor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm._at_purify x => SmtTermClosedIn vars x
  | SmtTerm.plus x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.neg x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mult x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.lt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.leq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.gt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.geq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.to_real x => SmtTermClosedIn vars x
  | SmtTerm.to_int x => SmtTermClosedIn vars x
  | SmtTerm.is_int x => SmtTermClosedIn vars x
  | SmtTerm.abs x => SmtTermClosedIn vars x
  | SmtTerm.uneg x => SmtTermClosedIn vars x
  | SmtTerm.div x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mod x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.multmult x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.divisible x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.int_pow2 x => SmtTermClosedIn vars x
  | SmtTerm.int_log2 x => SmtTermClosedIn vars x
  | SmtTerm.div_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mod_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.multmult_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.select x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.store x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.extract x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.repeat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnot x => SmtTermClosedIn vars x
  | SmtTerm.bvand x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnand x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvxor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvxnor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvcomp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvneg x => SmtTermClosedIn vars x
  | SmtTerm.bvadd x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvmul x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvudiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvurem x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsub x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsdiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsrem x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsmod x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvult x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvule x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvugt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvuge x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvslt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsle x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsgt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsge x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvshl x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvlshr x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvashr x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.zero_extend x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.sign_extend x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.rotate_left x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.rotate_right x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvuaddo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnego x => SmtTermClosedIn vars x
  | SmtTerm.bvsaddo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvumulo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsmulo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvusubo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvssubo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsdivo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.seq_empty _ => True
  | SmtTerm.str_len x => SmtTermClosedIn vars x
  | SmtTerm.str_concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_substr x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_contains x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_replace x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_indexof x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_at x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_prefixof x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_suffixof x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_rev x => SmtTermClosedIn vars x
  | SmtTerm.str_update x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_to_lower x => SmtTermClosedIn vars x
  | SmtTerm.str_to_upper x => SmtTermClosedIn vars x
  | SmtTerm.str_to_code x => SmtTermClosedIn vars x
  | SmtTerm.str_from_code x => SmtTermClosedIn vars x
  | SmtTerm.str_is_digit x => SmtTermClosedIn vars x
  | SmtTerm.str_to_int x => SmtTermClosedIn vars x
  | SmtTerm.str_from_int x => SmtTermClosedIn vars x
  | SmtTerm.str_lt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_leq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_replace_all x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_replace_re x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_replace_re_all x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_indexof_re x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.re_allchar => True
  | SmtTerm.re_none => True
  | SmtTerm.re_all => True
  | SmtTerm.str_to_re x => SmtTermClosedIn vars x
  | SmtTerm.re_mult x => SmtTermClosedIn vars x
  | SmtTerm.re_plus x => SmtTermClosedIn vars x
  | SmtTerm.re_exp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_opt x => SmtTermClosedIn vars x
  | SmtTerm.re_comp x => SmtTermClosedIn vars x
  | SmtTerm.re_range x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_inter x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_union x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_diff x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_loop x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_in_re x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.seq_unit x => SmtTermClosedIn vars x
  | SmtTerm.seq_nth x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_empty _ => True
  | SmtTerm.set_singleton x => SmtTermClosedIn vars x
  | SmtTerm.set_union x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_inter x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_minus x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_member x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_subset x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.qdiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.qdiv_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.int_to_bv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.ubv_to_int x => SmtTermClosedIn vars x
  | SmtTerm.sbv_to_int x => SmtTermClosedIn vars x

/-- A formula remains true when only SMT variable assignments are changed. -/
def StableInAnyVarModel (M : SmtModel) (P : Term) : Prop :=
  ∀ N, model_total_typed N -> model_agrees_on_globals M N ->
    eo_interprets N P true

/-- A formula remains true under variable-model changes whenever it is true. -/
def StableWhenTrueInAnyVarModel (P : Term) : Prop :=
  ∀ M, model_total_typed M -> eo_interprets M P true ->
    StableInAnyVarModel M P

theorem smt_interprets_of_model_eval_eq
    {M N : SmtModel} {t : SmtTerm} {b : Bool}
    (hEval : __smtx_model_eval M t = __smtx_model_eval N t) :
  smt_interprets M t b ->
    smt_interprets N t b :=
by
  intro h
  cases h with
  | intro_true hTy hTrue =>
      exact smt_interprets.intro_true N t hTy (by
        simpa [← hEval] using hTrue)
  | intro_false hTy hFalse =>
      exact smt_interprets.intro_false N t hTy (by
        simpa [← hEval] using hFalse)

theorem eo_interprets_of_smt_model_eval_eq
    {M N : SmtModel} {P : Term} {b : Bool}
    (hEval :
      __smtx_model_eval M (__eo_to_smt P) =
        __smtx_model_eval N (__eo_to_smt P)) :
  eo_interprets M P b ->
    eo_interprets N P b :=
by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  exact smt_interprets_of_model_eval_eq hEval

theorem stableWhenTrueInAnyVarModel_of_smt_model_eval_eq
    (P : Term)
    (hEval : ∀ M N : SmtModel,
      model_agrees_on_globals M N ->
        __smtx_model_eval M (__eo_to_smt P) =
          __smtx_model_eval N (__eo_to_smt P)) :
  StableWhenTrueInAnyVarModel P :=
by
  intro M _ hTrue N _ hAgree
  exact eo_interprets_of_smt_model_eval_eq (hEval M N hAgree) hTrue

/--
Closed EO formulas are stable under changes to SMT variable assignments.

The checker enforces this with `__eo_is_closed` on `assume` and `assume_push`;
this bridge turns that executable guard into the semantic invariant needed by
binder-sensitive rule proofs.
-/
axiom stableWhenTrueInAnyVarModel_of_closed :
  ∀ P, __eo_is_closed P = Term.Boolean true -> StableWhenTrueInAnyVarModel P

/--
Contextual truth for a derived formula.

The first field is the ordinary checker fact in the current model. The second
field is the freshness/parametricity fact needed by binder-sensitive rules:
the derived formula remains true in any model that only changes variables,
provided the same assumptions and local pushes hold there.
-/
structure ContextualTruth
    (M : SmtModel) (assumes pushes P : Term) : Prop where
  true_here :
    eo_interprets M assumes true ->
    eo_interprets M pushes true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N assumes true ->
      eo_interprets N pushes true ->
      eo_interprets N P true

/--
The premise evidence supplied to a rule.

Most rules only use `true_here`. Binder-sensitive congruence uses
`true_in_var_model`: the checker constructs that field only when the ambient
assumptions and pushes are known to remain true across variable-model changes.
-/
structure RulePremiseEvidence
    (M : SmtModel) (assumes pushes : Term) (premises : List Term) : Prop where
  true_here :
    AllInterpretedTrue M premises
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N premises

/-- Predicate asserting that every term in a list has an SMT translation. -/
def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_smt_translation t

/-- Predicate asserting that every term in a list has translated SMT Boolean type. -/
def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_bool_type t

/-- Predicate asserting that every term in a list has EO type `Bool`. -/
def AllTypeofBool (ts : List Term) : Prop :=
  ∀ t ∈ ts, __eo_typeof t = Term.Bool

/-- A term with EO type `Bool` cannot be `Stuck`. -/
theorem term_ne_stuck_of_typeof_bool
    {t : Term}
    (hTy : __eo_typeof t = Term.Bool) :
    t ≠ Term.Stuck := by
  intro hStuck
  rw [hStuck] at hTy
  have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact hStuckTy hTy

/-- Derives `premiseAndFormulaList_true` from `all_true`. -/
theorem premiseAndFormulaList_true_of_all_true
    (M : SmtModel) :
  ∀ premises : List Term,
    AllInterpretedTrue M premises ->
    eo_interprets M (premiseAndFormulaList premises) true :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_interprets_true M
  | cons p premises ih =>
      apply RuleProofs.eo_interprets_and_intro
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that a conjunction built from Boolean premises still has Boolean type. -/
theorem premiseAndFormulaList_has_bool_type :
  ∀ premises : List Term,
    AllHaveBoolType premises ->
    RuleProofs.eo_has_bool_type (premiseAndFormulaList premises) :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_has_bool_type_true
  | cons p premises ih =>
      apply RuleProofs.eo_has_bool_type_and_of_bool_args
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that `premiseAndFormulaList` is recognized as an `and`-list by `__eo_is_list`. -/
theorem premiseAndFormulaList_is_and_list :
  ∀ premises : List Term,
    __eo_is_list (Term.UOp UserOp.and) (premiseAndFormulaList premises) = Term.Boolean true
:=
by
  have hGetNil :
      ∀ premises : List Term,
        __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck
  :=
  by
    intro premises
    induction premises with
    | nil =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        unfold __eo_is_list_nil
        simp [native_ite, native_teq, native_not, SmtEval.native_not]
    | cons p premises ih =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        simpa [native_ite, native_teq, native_not, SmtEval.native_not] using ih
  intro premises
  have hNotStuck :
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck :=
    hGetNil premises
  have hPremNotStuck : premiseAndFormulaList premises ≠ Term.Stuck :=
    by
      induction premises with
      | nil =>
          simp [premiseAndFormulaList]
      | cons p premises ih =>
          simp [premiseAndFormulaList]
  unfold __eo_is_list
  unfold __eo_is_ok
  simpa [native_teq, native_not, SmtEval.native_not] using hNotStuck

/-- Establishes an equality relating `mk_premise_list_and` and `premiseAndFormulaList`. -/
theorem mk_premise_list_and_eq_premiseAndFormulaList :
  ∀ (s : CState) (premises : CIndexList),
    __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
      premiseAndFormulaList (premiseTermList s premises)
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_nil]
  | cons n premises ih =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_cons,
        __eo_requires, native_ite, native_teq, native_not, ih,
        premiseAndFormulaList_is_and_list, SmtEval.native_not]

/-- Structure bundling the correctness and translation obligations for rules that only add a proven fact. -/
structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    AllInterpretedTrue M premises ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/--
Richer rule-correctness template for rules whose soundness depends on more
than premise truth in the current model.

The old `StepRuleProperties` remains as a compatibility template for ordinary
rules. The checker bridge can lift ordinary rules into this shape by
re-instantiating their old proof at each variable-variant model.
-/
structure EvidenceStepRuleProperties
    (M : SmtModel) (assumes pushes : Term) (premises : List Term)
    (P : Term) : Prop where
  facts_of_evidence :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      RulePremiseEvidence N assumes pushes premises ->
      eo_interprets N P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Predicate packaging the correctness and translation obligations for rules that also pop assumptions. -/
def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    RuleProofs.eo_has_smt_translation P
