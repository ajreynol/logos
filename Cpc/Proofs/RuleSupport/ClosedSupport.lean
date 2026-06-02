import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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

theorem model_agrees_on_env_nil_of_globals
    {M N : SmtModel} :
  model_agrees_on_globals M N ->
    model_agrees_on_env [] M N :=
by
  intro hAgree
  exact ⟨hAgree, by intro s T hMem; cases hMem⟩

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

theorem native_model_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    (s : native_String) (T : SmtType) :
  native_model_lookup M s T =
    native_model_lookup N s T :=
by
  exact hAgree.globals.1 s T

theorem native_model_fun_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    (fid : native_String) (T U : SmtType) :
  native_model_fun_lookup M fid T U =
    native_model_fun_lookup N fid T U :=
by
  exact hAgree.globals.2 fid T U

theorem native_model_var_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    {s : native_String} {T : SmtType}
    (hMem : (s, T) ∈ vars) :
  native_model_var_lookup M s T =
    native_model_var_lookup N s T :=
by
  exact hAgree.vars_eq s T hMem

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

theorem eo_and_eq_true_cases {a b : Term} :
  __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true :=
by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at h ⊢
  case Binary.Binary =>
    split at h <;> contradiction

/-- Relation between an EO list of variables and the corresponding SMT binder stack. -/
inductive EoSmtVarEnv : Term -> List SmtVarKey -> Prop where
  | nil :
      EoSmtVarEnv Term.__eo_List_nil []
  | cons {s : native_String} {T env : Term} {vars : List SmtVarKey} :
      EoSmtVarEnv env vars ->
        EoSmtVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env)
          ((s, __eo_to_smt_type T) :: vars)

theorem EoSmtVarEnv.get_nil_ok :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        __eo_is_ok (__eo_get_nil_rec Term.__eo_List_cons env) =
          Term.Boolean true
  | _, _, EoSmtVarEnv.nil =>
      by
        simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
          __eo_is_ok, native_ite, native_teq, native_not]
  | _, _, EoSmtVarEnv.cons hTail =>
      by
        simpa [__eo_get_nil_rec, __eo_requires, __eo_is_ok,
          native_ite, native_teq, native_not] using hTail.get_nil_ok

theorem EoSmtVarEnv.is_list :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        __eo_is_list Term.__eo_List_cons env = Term.Boolean true
  | _, _, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_is_list] using EoSmtVarEnv.get_nil_ok EoSmtVarEnv.nil
        | cons hTail =>
            simpa [__eo_is_list] using
              EoSmtVarEnv.get_nil_ok (EoSmtVarEnv.cons hTail)

theorem EoSmtVarEnv.cons_mk_apply
    {s : native_String} {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  EoSmtVarEnv
    (__eo_mk_apply
      (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      env)
    ((s, __eo_to_smt_type T) :: vars) :=
by
  cases hEnv with
  | nil =>
      simpa [__eo_mk_apply] using
        EoSmtVarEnv.cons (s := s) (T := T) EoSmtVarEnv.nil
  | cons hTail =>
      simpa [__eo_mk_apply] using
        EoSmtVarEnv.cons (s := s) (T := T)
          (EoSmtVarEnv.cons hTail)

theorem EoSmtVarEnv.concat_rec :
    ∀ {vs env : Term} {binderVars vars : List SmtVarKey},
      EoSmtVarEnv vs binderVars ->
        EoSmtVarEnv env vars ->
          EoSmtVarEnv (__eo_list_concat_rec vs env) (binderVars ++ vars)
  | _, _, _, _, EoSmtVarEnv.nil, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec] using EoSmtVarEnv.nil
        | cons hTail =>
            simpa [__eo_list_concat_rec] using EoSmtVarEnv.cons hTail
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec, List.cons_append]
              using EoSmtVarEnv.cons_mk_apply
                (s := s) (T := T)
                (EoSmtVarEnv.concat_rec hTail EoSmtVarEnv.nil)
        | cons hEnvTail =>
            simpa [__eo_list_concat_rec, List.cons_append]
              using EoSmtVarEnv.cons_mk_apply
                (s := s) (T := T)
                (EoSmtVarEnv.concat_rec hTail (EoSmtVarEnv.cons hEnvTail))

theorem EoSmtVarEnv.concat :
    ∀ {vs env : Term} {binderVars vars : List SmtVarKey},
      EoSmtVarEnv vs binderVars ->
        EoSmtVarEnv env vars ->
          EoSmtVarEnv
            (__eo_list_concat Term.__eo_List_cons vs env)
            (binderVars ++ vars)
  | _, _, _, _, hVs, hEnv =>
      by
        have hVsList := hVs.is_list
        have hEnvList := hEnv.is_list
        simpa [__eo_list_concat, __eo_requires, hVsList, hEnvList,
          native_ite, native_teq]
          using EoSmtVarEnv.concat_rec hVs hEnv

theorem EoSmtVarEnv.mem_of_closed_var :
    ∀ {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term},
      EoSmtVarEnv env vars ->
        __eo_is_closed_rec (Term.Var (Term.String s) T) env =
          Term.Boolean true ->
          (s, __eo_to_smt_type T) ∈ vars
  | _, _, _, _, EoSmtVarEnv.nil, hClosed =>
      by
        simp [__eo_is_closed_rec] at hClosed
  | _, _, s, T, EoSmtVarEnv.cons (s := s') (T := T') hTail, hClosed =>
      by
        by_cases hVarEq :
            Term.Var (Term.String s') T' =
              Term.Var (Term.String s) T
        · injection hVarEq with hName hTy
          injection hName with hs
          cases hs
          cases hTy
          simp
        · right
          exact EoSmtVarEnv.mem_of_closed_var hTail (by
            simpa [__eo_is_closed_rec, __eo_ite, __eo_eq, hVarEq,
              native_ite, native_teq] using hClosed)

/-- Two SMT variable stacks expose the same bound variables. -/
def SmtVarEnvEquiv (xs ys : List SmtVarKey) : Prop :=
  ∀ key, key ∈ xs ↔ key ∈ ys

theorem SmtVarEnvEquiv.refl (xs : List SmtVarKey) :
  SmtVarEnvEquiv xs xs :=
by
  intro key
  rfl

theorem SmtVarEnvEquiv.reverse (xs : List SmtVarKey) :
  SmtVarEnvEquiv xs xs.reverse :=
by
  intro key
  simp

theorem SmtVarEnvEquiv.append
    {xs xs' ys ys' : List SmtVarKey}
    (hxs : SmtVarEnvEquiv xs xs')
    (hys : SmtVarEnvEquiv ys ys') :
  SmtVarEnvEquiv (xs ++ ys) (xs' ++ ys') :=
by
  intro key
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).1 h))
    · exact List.mem_append.2 (Or.inr ((hys key).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).2 h))
    · exact List.mem_append.2 (Or.inr ((hys key).2 h))

/--
Order-insensitive EO/SMT environment relation.

`__eo_is_closed_rec` only cares whether a variable appears in the EO list, while
SMT quantifier translation reverses binder order as it nests binders. This
wrapper lets those two views share the same membership facts.
-/
def EoSmtVarEnvPerm (env : Term) (vars : List SmtVarKey) : Prop :=
  ∃ exactVars, EoSmtVarEnv env exactVars ∧ SmtVarEnvEquiv exactVars vars

theorem EoSmtVarEnvPerm.of_exact
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  EoSmtVarEnvPerm env vars :=
by
  exact ⟨vars, hEnv, SmtVarEnvEquiv.refl vars⟩

theorem EoSmtVarEnvPerm.mem_of_closed_var
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  (s, __eo_to_smt_type T) ∈ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  exact (hEquiv (s, __eo_to_smt_type T)).1
    (EoSmtVarEnv.mem_of_closed_var hExact hClosed)

theorem EoSmtVarEnvPerm.concat_rev
    {vs env : Term} {binderVars vars : List SmtVarKey}
    (hVs : EoSmtVarEnv vs binderVars)
    (hEnv : EoSmtVarEnvPerm env vars) :
  EoSmtVarEnvPerm
    (__eo_list_concat Term.__eo_List_cons vs env)
    (binderVars.reverse ++ vars) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  refine ⟨binderVars ++ exactVars, EoSmtVarEnv.concat hVs hExact, ?_⟩
  exact SmtVarEnvEquiv.append
    (SmtVarEnvEquiv.reverse binderVars)
    hEquiv

theorem eo_is_closed_rec_apply_uop_arg_eq_true
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact (eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)).2
  | cons hTail =>
      exact (eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)).2

theorem eo_is_closed_rec_binary_uop_eq_true_cases
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hEnv' : EoSmtVarEnvPerm Term.__eo_List_nil vars :=
        ⟨_, EoSmtVarEnv.nil, hEquiv⟩
      have hOuter := eo_and_eq_true_cases
        (by
          simpa [__eo_is_closed_rec, hNotForall, hNotExists]
            using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.2, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by
          simpa [__eo_is_closed_rec, hNotForall, hNotExists]
            using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.2, hOuter.2⟩

theorem smtTermClosedIn_eo_to_smt_boolean
    (vars : List SmtVarKey) (b : native_Bool) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Boolean b)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_numeral
    (vars : List SmtVarKey) (n : native_Int) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Numeral n)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_rational
    (vars : List SmtVarKey) (r : native_Rat) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Rational r)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_string
    (vars : List SmtVarKey) (s : native_String) :
  SmtTermClosedIn vars (__eo_to_smt (Term.String s)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_binary
    (vars : List SmtVarKey) (w n : native_Int) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Binary w n)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_var_string
    {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hMem : (s, __eo_to_smt_type T) ∈ vars) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact hMem

theorem smtTermClosedIn_eo_to_smt_var_string_of_closed_rec
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact smtTermClosedIn_eo_to_smt_var_string
    (EoSmtVarEnv.mem_of_closed_var hEnv hClosed)

theorem smtTermClosedIn_eo_to_smt_var_string_of_closed_rec_perm
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact smtTermClosedIn_eo_to_smt_var_string
    (EoSmtVarEnvPerm.mem_of_closed_var hEnv hClosed)

theorem smtTermClosedIn_eo_to_smt_not
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_and
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_or
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_imp
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_xor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_eq
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_not_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  exact smtTermClosedIn_eo_to_smt_not
    (hRec hEnv
      (eo_is_closed_rec_apply_uop_arg_eq_true hEnv hClosed))

theorem smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  have hCases :=
    eo_is_closed_rec_binary_uop_eq_true_cases
      hNotForall hNotExists hEnv hClosed
  exact hBuilder (hRecX hEnv hCases.1) (hRecY hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_and_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.and) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_and hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_or_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.or) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_or hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_imp_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.imp) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_imp hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_xor_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.xor) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_xor hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_eq_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.eq) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_eq hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_exists_nil
    {vars : List SmtVarKey} {F : SmtTerm}
    (hF : SmtTermClosedIn vars F) :
  SmtTermClosedIn vars (__eo_to_smt_exists Term.__eo_List_nil F) :=
by
  exact hF

theorem smtTermClosedIn_eo_to_smt_exists_cons
    {vars : List SmtVarKey} {s : native_String} {T : Term}
    {vs : Term} {F : SmtTerm}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs F)) :
  SmtTermClosedIn vars
    (__eo_to_smt_exists
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) vs)
      F) :=
by
  exact hBody

theorem smtTermClosedIn_eo_to_smt_exists_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {F : SmtTerm},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) F ->
          SmtTermClosedIn vars (__eo_to_smt_exists vs F)
  | _, _, _, _, EoSmtVarEnv.nil, hF =>
      by
        simpa using hF
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hF =>
      by
        exact smtTermClosedIn_eo_to_smt_exists_cons
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env hTail (by
            simpa [List.reverse_cons, List.append_assoc] using hF))

theorem smtTermClosedIn_eo_to_smt_exists_cons_term
    {vars : List SmtVarKey} {s : native_String} {T vs body : Term}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs (__eo_to_smt body))) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.exists)
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) vs))
        body)) :=
by
  exact hBody

theorem smtTermClosedIn_eo_to_smt_exists_nil_term
    {vars : List SmtVarKey} {body : Term} :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil)
        body)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_exists_term_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {body : Term},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body) ->
          SmtTermClosedIn vars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body))
  | _, _, _, _, EoSmtVarEnv.nil, hBody =>
      by
        trivial
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hBody =>
      by
        exact smtTermClosedIn_eo_to_smt_exists_cons_term
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env hTail (by
            simpa [List.reverse_cons, List.append_assoc] using hBody))

theorem smtTermClosedIn_eo_to_smt_forall_nil
    {vars : List SmtVarKey} {body : Term} :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil)
        body)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_forall_cons_term
    {vars : List SmtVarKey} {s : native_String} {T vs body : Term}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body)))) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.forall)
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) vs))
        body)) :=
by
  exact hBody

theorem smtTermClosedIn_eo_to_smt_forall_term_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {body : Term},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body) ->
          SmtTermClosedIn vars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body))
  | _, _, _, _, EoSmtVarEnv.nil, hBody =>
      by
        trivial
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hBody =>
      by
        exact smtTermClosedIn_eo_to_smt_forall_cons_term
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env hTail (by
            simpa [List.reverse_cons, List.append_assoc] using hBody))

theorem smtTermClosedIn_eo_to_smt_exists_of_closed_rec_using
    {vs body env : Term} {binderVars vars : List SmtVarKey}
    (hVs : EoSmtVarEnv vs binderVars)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec body env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt body))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body)) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact smtTermClosedIn_eo_to_smt_exists_term_of_rev_env hVs
        (hRec
          (EoSmtVarEnvPerm.concat_rev hVs
            ⟨_, EoSmtVarEnv.nil, hEquiv⟩)
          (by simpa [__eo_is_closed_rec] using hClosed))
  | cons hTail =>
      exact smtTermClosedIn_eo_to_smt_exists_term_of_rev_env hVs
        (hRec
          (EoSmtVarEnvPerm.concat_rev hVs
            ⟨_, EoSmtVarEnv.cons hTail, hEquiv⟩)
          (by simpa [__eo_is_closed_rec] using hClosed))

theorem smtTermClosedIn_eo_to_smt_forall_of_closed_rec_using
    {vs body env : Term} {binderVars vars : List SmtVarKey}
    (hVs : EoSmtVarEnv vs binderVars)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec body env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt body))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact smtTermClosedIn_eo_to_smt_forall_term_of_rev_env hVs
        (hRec
          (EoSmtVarEnvPerm.concat_rev hVs
            ⟨_, EoSmtVarEnv.nil, hEquiv⟩)
          (by simpa [__eo_is_closed_rec] using hClosed))
  | cons hTail =>
      exact smtTermClosedIn_eo_to_smt_forall_term_of_rev_env hVs
        (hRec
          (EoSmtVarEnvPerm.concat_rev hVs
            ⟨_, EoSmtVarEnv.cons hTail, hEquiv⟩)
          (by simpa [__eo_is_closed_rec] using hClosed))

theorem smtTermClosedIn_smt_apply
    {vars : List SmtVarKey} {f x : SmtTerm}
    (hf : SmtTermClosedIn vars f)
    (hx : SmtTermClosedIn vars x) :
  SmtTermClosedIn vars (SmtTerm.Apply f x) :=
by
  exact ⟨hf, hx⟩

theorem smtTermClosedIn_smt_not
    {vars : List SmtVarKey} {x : SmtTerm}
    (hx : SmtTermClosedIn vars x) :
  SmtTermClosedIn vars (SmtTerm.not x) :=
by
  exact hx

theorem smtTermClosedIn_smt_and
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.and x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_or
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.or x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_eq
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.eq x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_exists
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.exists s T body) :=
by
  exact hBody

theorem smtTermClosedIn_smt_forall
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.forall s T body) :=
by
  exact hBody

theorem smtTermClosedIn_smt_choice_nth
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm} {n : native_Nat}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.choice_nth s T body n) :=
by
  exact hBody

theorem smtx_model_eval_var_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType}
    (hAgree : model_agrees_on_env vars M N)
    (hClosed : SmtTermClosedIn vars (SmtTerm.Var s T)) :
  __smtx_model_eval M (SmtTerm.Var s T) =
    __smtx_model_eval N (SmtTerm.Var s T) :=
by
  simp [__smtx_model_eval, native_model_var_lookup_eq_of_env hAgree hClosed]

theorem smtx_model_eval_uconst_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType}
    (hAgree : model_agrees_on_env vars M N) :
  __smtx_model_eval M (SmtTerm.UConst s T) =
    __smtx_model_eval N (SmtTerm.UConst s T) :=
by
  simp [__smtx_model_eval, native_model_lookup_eq_of_env hAgree]

theorem smtx_model_eval_apply_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel} {f x : SmtTerm}
    (hAgree : model_agrees_on_env vars M N)
    (hf :
      __smtx_model_eval M f = __smtx_model_eval N f)
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x) :
  __smtx_model_eval M (SmtTerm.Apply f x) =
    __smtx_model_eval N (SmtTerm.Apply f x) :=
by
  cases f <;>
    simp [__smtx_model_eval, hf, hx,
      smtx_model_eval_apply_eq_of_globals hAgree.globals,
      smtx_model_eval_dt_sel_eq_of_globals hAgree.globals]

theorem smtx_model_eval_not_eq_of_eval_eq
    {M N : SmtModel} {x : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x) :
  __smtx_model_eval M (SmtTerm.not x) =
    __smtx_model_eval N (SmtTerm.not x) :=
by
  simp [__smtx_model_eval, hx]

theorem smtx_model_eval_and_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.and x y) =
    __smtx_model_eval N (SmtTerm.and x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_or_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.or x y) =
    __smtx_model_eval N (SmtTerm.or x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_imp_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.imp x y) =
    __smtx_model_eval N (SmtTerm.imp x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_xor_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.xor x y) =
    __smtx_model_eval N (SmtTerm.xor x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_eq_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.eq x y) =
    __smtx_model_eval N (SmtTerm.eq x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_exists_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  __smtx_model_eval M (SmtTerm.exists s T body) =
    __smtx_model_eval N (SmtTerm.exists s T body) :=
by
  simp [__smtx_model_eval, native_eval_texists_eq_of_body_eval_eq hBody]

theorem smtx_model_eval_forall_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  __smtx_model_eval M (SmtTerm.forall s T body) =
    __smtx_model_eval N (SmtTerm.forall s T body) :=
by
  simp [__smtx_model_eval, native_eval_tforall_eq_of_body_eval_eq hBody]

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
Remaining translation invariant for closed EO formulas.

Executable EO closedness should imply closedness of the translated SMT term in
the empty SMT-variable environment.
-/
axiom smtTermClosedIn_of_eo_is_closed :
  ∀ P, __eo_is_closed P = Term.Boolean true ->
    SmtTermClosedIn [] (__eo_to_smt P)

/--
Remaining structural SMT evaluator invariant.

If two models agree on all globals and on the currently bound SMT variables,
then every SMT term closed in that environment evaluates identically in them.
-/
axiom smt_model_eval_eq_of_closedIn :
  ∀ (t : SmtTerm) (vars : List SmtVarKey) (M N : SmtModel),
    SmtTermClosedIn vars t ->
      model_agrees_on_env vars M N ->
        __smtx_model_eval M t = __smtx_model_eval N t

theorem smt_model_eval_eq_of_eo_closed_in_empty_env
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true)
    (M N : SmtModel) (hAgree : model_agrees_on_env [] M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_closedIn (__eo_to_smt P) [] M N
    (smtTermClosedIn_of_eo_is_closed P hClosed) hAgree

theorem smt_model_eval_eq_of_eo_smt_closed
    {P : Term} {M N : SmtModel}
    (hClosed : SmtTermClosedIn [] (__eo_to_smt P))
    (hAgree : model_agrees_on_globals M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_closedIn (__eo_to_smt P) [] M N hClosed
    (model_agrees_on_env_nil_of_globals hAgree)

/-- Closed EO formula evaluation is insensitive to variable-model changes. -/
theorem smt_model_eval_eq_of_eo_closed
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true)
    (M N : SmtModel) (hAgree : model_agrees_on_globals M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_eo_closed_in_empty_env P hClosed M N
    (model_agrees_on_env_nil_of_globals hAgree)

/--
Closed EO formulas are stable under changes to SMT variable assignments.

This is now derived from `smt_model_eval_eq_of_eo_closed`; the remaining proof
work is the evaluator invariant, not the high-level checker stability property.
-/
theorem stableWhenTrueInAnyVarModel_of_closed
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true) :
  StableWhenTrueInAnyVarModel P :=
by
  exact stableWhenTrueInAnyVarModel_of_smt_model_eval_eq P
    (fun M N hAgree => smt_model_eval_eq_of_eo_closed P hClosed M N hAgree)
