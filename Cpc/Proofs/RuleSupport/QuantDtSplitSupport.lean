import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.DatatypeSupport
import Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import Cpc.Proofs.TypePreservation

open Eo
open SmtEval
open Smtm

/-!
Support lemmas for the rule `quant_dt_split`:

* list-view spine decomposition of SMT values and the reconstruction form of
  datatype exhaustiveness (`datatype_value_spine`);
* the two-sided truth characterization of a translated universal quantifier
  (`forall_encoding_true_iff`);
* syntactic reification of the guard (`ConjRel`/`SplitRel`) with extraction
  from a successful run (`conjRel_of_guard_true`, `splitRel_of_guard_true`).
-/

namespace QuantDtSplitRule

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open InstantiateRule

/-- Application spine, accumulator style: `vsmMkSpine h [a, b] = Apply (Apply h a) b`. -/
def vsmMkSpine (head : SmtValue) : List SmtValue -> SmtValue
  | [] => head
  | a :: args => vsmMkSpine (SmtValue.Apply head a) args

/-- The arguments of a value's application spine, outermost last. -/
def vsmArgs : SmtValue -> List SmtValue
  | SmtValue.Apply f a => vsmArgs f ++ [a]
  | _ => []

@[simp] theorem vsmMkSpine_nil (h : SmtValue) : vsmMkSpine h [] = h := rfl

@[simp] theorem vsmMkSpine_cons (h a : SmtValue) (args : List SmtValue) :
    vsmMkSpine h (a :: args) = vsmMkSpine (SmtValue.Apply h a) args := rfl

theorem vsmMkSpine_append_singleton (args : List SmtValue) :
    ∀ (h a : SmtValue), vsmMkSpine h (args ++ [a]) = SmtValue.Apply (vsmMkSpine h args) a := by
  induction args with
  | nil => intro h a; rfl
  | cons b args ih =>
      intro h a
      rw [List.cons_append, vsmMkSpine_cons, vsmMkSpine_cons, ih]

/-- Every value is the spine of its head applied to its arguments. -/
theorem vsm_spine_decomposition :
    ∀ v : SmtValue, v = vsmMkSpine (__vsm_apply_head v) (vsmArgs v)
  | SmtValue.Apply f a => by
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl,
        show __vsm_apply_head (SmtValue.Apply f a) = __vsm_apply_head f from rfl,
        vsmMkSpine_append_singleton]
      exact congrArg (SmtValue.Apply · a) (vsm_spine_decomposition f)
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

theorem vsmArgs_length : ∀ v : SmtValue, (vsmArgs v).length = vsm_num_apply_args v
  | SmtValue.Apply f a => by
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl,
        show vsm_num_apply_args (SmtValue.Apply f a) = Nat.succ (vsm_num_apply_args f) from rfl,
        List.length_append, vsmArgs_length f]
      simp
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

/-- The index-based accessor reads the list view. -/
theorem vsm_apply_arg_nth_eq_getElem :
    ∀ (v : SmtValue) (j : Nat), j < (vsmArgs v).length ->
      __vsm_apply_arg_nth v j (vsm_num_apply_args v) = (vsmArgs v)[j]!
  | SmtValue.Apply f a => by
      intro j hj
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl] at hj ⊢
      rw [show vsm_num_apply_args (SmtValue.Apply f a) = Nat.succ (vsm_num_apply_args f) from rfl,
        show __vsm_apply_arg_nth (SmtValue.Apply f a) j (Nat.succ (vsm_num_apply_args f)) =
          native_ite (native_nateq j (vsm_num_apply_args f)) a
            (__vsm_apply_arg_nth f j (vsm_num_apply_args f)) from rfl]
      by_cases hEq : j = vsm_num_apply_args f
      · have hbeq : native_nateq j (vsm_num_apply_args f) = true := by
          simp [native_nateq, hEq]
        rw [hbeq]
        have hj' : j = (vsmArgs f).length := by rw [vsmArgs_length f]; exact hEq
        subst hj'
        have : (vsmArgs f ++ [a])[(vsmArgs f).length]! = a := by simp
        rw [this]
        rfl
      · have hbeq : native_nateq j (vsm_num_apply_args f) = false := by
          simp [native_nateq, hEq]
        rw [hbeq]
        have hjf : j < (vsmArgs f).length := by
          rw [List.length_append] at hj
          rw [vsmArgs_length f]
          rw [vsmArgs_length f] at hj
          simp at hj
          omega
        have : (vsmArgs f ++ [a])[j]! = (vsmArgs f)[j]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left hjf]
        rw [this, ← vsm_apply_arg_nth_eq_getElem f j hjf]
        rfl
  | SmtValue.NotValue => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Boolean _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Numeral _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Rational _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Binary _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Map _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Fun _ _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Set _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Seq _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Char _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.UValue _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.RegLan _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.DtCons _ _ _ => by intro j hj; simp [vsmArgs] at hj

/-- Canonicity of a spine gives canonicity of head and all arguments. -/
theorem vsm_canonical_spine :
    ∀ v : SmtValue,
      __smtx_value_canonical_bool v = true ->
      __smtx_value_canonical_bool (__vsm_apply_head v) = true ∧
        ∀ a ∈ vsmArgs v, __smtx_value_canonical_bool a = true
  | SmtValue.Apply f a => by
      intro hCanon
      rw [show __smtx_value_canonical_bool (SmtValue.Apply f a) =
        native_and (__smtx_value_canonical_bool f) (__smtx_value_canonical_bool a) from rfl]
        at hCanon
      have hf : __smtx_value_canonical_bool f = true := by
        cases hcf : __smtx_value_canonical_bool f
        · rw [hcf] at hCanon; cases hCanon
        · rfl
      have ha : __smtx_value_canonical_bool a = true := by
        rw [hf] at hCanon
        cases hca : __smtx_value_canonical_bool a
        · rw [hca] at hCanon; cases hCanon
        · rfl
      obtain ⟨hHead, hArgs⟩ := vsm_canonical_spine f hf
      refine ⟨hHead, ?_⟩
      intro b hb
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl] at hb
      rcases List.mem_append.1 hb with hbf | hba
      · exact hArgs b hbf
      · rw [List.mem_singleton.1 hba]; exact ha
  | SmtValue.NotValue => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Boolean _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Numeral _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Rational _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Binary _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Map _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Fun _ _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Set _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Seq _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Char _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.UValue _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.RegLan _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.DtCons _ _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩

/-- Canonicity of a spine from canonicity of head and arguments (converse). -/
theorem vsm_canonical_of_spine (args : List SmtValue) :
    ∀ head : SmtValue,
      __smtx_value_canonical_bool head = true ->
      (∀ a ∈ args, __smtx_value_canonical_bool a = true) ->
      __smtx_value_canonical_bool (vsmMkSpine head args) = true := by
  induction args with
  | nil => intro head hHead _; simpa using hHead
  | cons a args ih =>
      intro head hHead hArgs
      rw [vsmMkSpine_cons]
      refine ih (SmtValue.Apply head a) ?_ ?_
      · rw [show __smtx_value_canonical_bool (SmtValue.Apply head a) =
          native_and (__smtx_value_canonical_bool head) (__smtx_value_canonical_bool a) from rfl,
          hHead, hArgs a (List.mem_cons_self ..)]
        rfl
      · intro b hb
        exact hArgs b (List.mem_cons_of_mem a hb)

/--
Reconstruction form of datatype exhaustiveness: every value of a datatype sort
is a constructor spine with in-range index, correct arity, and arguments typed
by the (substituted) selector types.
-/
theorem datatype_value_spine
    {v : SmtValue} {s : native_String} {d : SmtDatatype}
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ (i : Nat) (args : List SmtValue),
      v = vsmMkSpine (SmtValue.DtCons s d i) args ∧
      i < smtDatatypeNumCtors d ∧
      args.length = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i ∧
      (∀ j : Nat, j < args.length ->
        __smtx_typeof_value args[j]! =
          __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j) := by
  obtain ⟨i, hHead⟩ := datatype_value_head_of_type hTy
  refine ⟨i, vsmArgs v, ?_, ?_, ?_, ?_⟩
  · have := vsm_spine_decomposition v
    rwa [hHead] at this
  · exact datatype_head_index_lt hHead hTy
  · rw [vsmArgs_length]
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  · intro j hj
    have hjn : j < vsm_num_apply_args v := by rwa [vsmArgs_length] at hj
    have hNone : __smtx_typeof_value v ≠ SmtType.None := by
      rw [hTy]; intro h; cases h
    have := apply_arg_nth_type_of_non_none hHead hNone hjn
    rw [vsm_apply_arg_nth_eq_getElem v j hj] at this
    exact this

/-! ## Truth characterization of translated universals -/


theorem smtx_model_eval_not_unfold (M : SmtModel) (t : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not t) =
      __smtx_model_eval_not (__smtx_model_eval M t) := by
  simp only [__smtx_model_eval]

/-- Introduction direction: body true under every instantiation makes the
    encoded forall true. -/
theorem forall_encoding_true_of_all_inst
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf : ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    ∀ M : SmtModel, model_total_typed M ->
    (∀ N, ForallInstantiationModel M xs N ->
      __smtx_model_eval N body = SmtValue.Boolean true) ->
    __smtx_model_eval M (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
      SmtValue.Boolean true := by
  classical
  induction hEnv with
  | nil =>
      intro M _hM h
      have hBody : __smtx_model_eval M body = SmtValue.Boolean true :=
        h M (ForallInstantiationModel.nil M)
      rw [show __eo_to_smt_exists Term.__eo_List_nil (SmtTerm.not body) =
        SmtTerm.not body from rfl]
      rw [smtx_model_eval_not_unfold, smtx_model_eval_not_unfold, hBody]
      rfl
  | cons hTail ih =>
      rename_i s T env tailVars
      intro M hM h
      rw [show __eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env) (SmtTerm.not body) =
        SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists env (SmtTerm.not body)) from rfl]
      have hHeadWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf s T (List.Mem.head _)
      have hnP : ¬ (∃ v : SmtValue,
          __smtx_typeof_value v = __eo_to_smt_type T ∧
            __smtx_value_canonical_bool v = true ∧
              __smtx_model_eval
                (native_model_push M s (__eo_to_smt_type T) v)
                (__eo_to_smt_exists env (SmtTerm.not body)) =
                SmtValue.Boolean true) := by
        rintro ⟨v, hvT, hvC, hvE⟩
        have hPushTotal :
            model_total_typed (native_model_push M s (__eo_to_smt_type T) v) :=
          model_total_typed_push hM s (__eo_to_smt_type T) v hHeadWf hvT
            (by simpa [__smtx_value_canonical] using hvC)
        have hInner :
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
              (SmtTerm.not (__eo_to_smt_exists env (SmtTerm.not body))) =
              SmtValue.Boolean true := by
          refine ih
            (by
              intro s' T' hMem
              exact hWf s' T' (List.Mem.tail _ hMem))
            (native_model_push M s (__eo_to_smt_type T) v) hPushTotal ?_
          intro N hInst
          exact h N (ForallInstantiationModel.cons hHeadWf hvT hvC hInst)
        rw [smtx_model_eval_not_unfold] at hInner
        have hFalse :
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
              (__eo_to_smt_exists env (SmtTerm.not body)) =
              SmtValue.Boolean false :=
          (smtx_model_eval_not_true_iff _).1 hInner
        rw [hFalse] at hvE
        exact absurd hvE (by decide)
      have hExFalse :
          __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env (SmtTerm.not body))) =
            SmtValue.Boolean false := by
        show (if _ : (∃ v : SmtValue,
            __smtx_typeof_value v = __eo_to_smt_type T ∧
              __smtx_value_canonical_bool v = true ∧
                __smtx_model_eval
                  (native_model_push M s (__eo_to_smt_type T) v)
                  (__eo_to_smt_exists env (SmtTerm.not body)) =
                  SmtValue.Boolean true)
          then SmtValue.Boolean true else SmtValue.Boolean false) =
          SmtValue.Boolean false
        rw [dif_neg hnP]
      rw [smtx_model_eval_not_unfold, hExFalse]
      rfl

/-- Two-sided characterization of the truth of an encoded universal. -/
theorem forall_encoding_true_iff
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf : ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (M : SmtModel) (hM : model_total_typed M) :
    __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true ↔
      ∀ N, ForallInstantiationModel M xs N ->
        __smtx_model_eval N body = SmtValue.Boolean true := by
  constructor
  · intro hEval N hInst
    exact forall_instantiation_body_true hInst hM hBodyTy hEval
  · exact forall_encoding_true_of_all_inst hEnv hWf hBodyTy M hM

/-! ## Guard reification -/

/-- `cons` cell of an EO list. -/
abbrev eoCons (a l : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons a) l

/-- EO `forall` with binder list `vs` and body `B`. -/
abbrev mkForall (vs B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) B

/-- EO `and` application. -/
abbrev mkAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

/-- Singleton-list substitution of `x` by `t` in `F` as used by the guard. -/
abbrev substOne (x t F : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) F
    (eoCons x Term.__eo_List_nil) (eoCons t Term.__eo_List_nil)
    Term.__eo_List_nil

/-! ### Eliminators for the EO control primitives -/

theorem eo_requires_boolean_true_elim {a b c : Term}
    (h : __eo_requires a b c = Term.Boolean true) :
    a = b ∧ a ≠ Term.Stuck ∧ c = Term.Boolean true := by
  rw [__eo_requires] at h
  by_cases hab : native_teq a b = true
  · rw [hab] at h
    simp only [native_ite, if_true] at h
    by_cases hStuck : native_teq a Term.Stuck = true
    · rw [hStuck] at h
      simp [native_not] at h
    · have : native_teq a Term.Stuck = false := by
        cases hv : native_teq a Term.Stuck
        · rfl
        · exact absurd hv hStuck
      rw [this] at h
      simp only [native_not, Bool.not_false, native_ite, if_true] at h
      refine ⟨by simpa [native_teq] using hab, ?_, h⟩
      intro hEq
      rw [hEq] at this
      simp [native_teq] at this
  · have : native_teq a b = false := by
      cases hv : native_teq a b
      · rfl
      · exact absurd hv hab
    rw [this] at h
    simp only [native_ite, if_false] at h
    cases h

theorem eo_ite_boolean_true_elim {c t e : Term}
    (h : __eo_ite c t e = Term.Boolean true) :
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  rw [__eo_ite] at h
  by_cases hc : native_teq c (Term.Boolean true) = true
  · left
    refine ⟨by simpa [native_teq] using hc, ?_⟩
    rw [hc] at h
    exact h
  · have hcf : native_teq c (Term.Boolean true) = false := by
      cases hv : native_teq c (Term.Boolean true)
      · rfl
      · exact absurd hv hc
    rw [hcf] at h
    simp only [native_ite, if_false] at h
    by_cases hc2 : native_teq c (Term.Boolean false) = true
    · right
      refine ⟨by simpa [native_teq] using hc2, ?_⟩
      rw [hc2] at h
      exact h
    · have hc2f : native_teq c (Term.Boolean false) = false := by
        cases hv : native_teq c (Term.Boolean false)
        · rfl
        · exact absurd hv hc2
      rw [hc2f] at h
      simp at h

theorem eo_eq_boolean_true_elim {a b : Term}
    (h : __eo_eq a b = Term.Boolean true) : a = b := by
  fun_cases __eo_eq a b <;> simp_all [__eo_eq, native_teq]

/-! ### The reified guard relations -/

/--
Reified successful run of `__is_quant_dt_split_conj x c ys F g`.

Constructors mirror the arms of the (fixed) guard:
- `peel`: consume a retained binder present in both `ys` and the conjunct's
  binder list (no later shadowing).
- `absorb`: `ys` exhausted; absorb the conjunct's next binder as a constructor
  argument (no later shadowing, not free in `F`).
- `unwrap`: the conjunct's binder list is exhausted; continue in its body.
- `final`: the remaining conjunct is exactly the substituted body.
-/
inductive ConjRel (x F : Term) : Term -> Term -> Term -> Prop where
  | peel {c y ys zs G : Term} :
      __eo_list_find Term.__eo_List_cons zs y = Term.Numeral (-1 : native_Int) ->
      ConjRel x F c ys (mkForall zs G) ->
      ConjRel x F c (eoCons y ys) (mkForall (eoCons y zs) G)
  | absorb {c y zs G : Term} :
      __eo_list_find Term.__eo_List_cons zs y = Term.Numeral (-1 : native_Int) ->
      __contains_atomic_term_list_free_rec F (eoCons y Term.__eo_List_nil)
        Term.__eo_List_nil = Term.Boolean false ->
      ConjRel x F (Term.Apply c y) Term.__eo_List_nil (mkForall zs G) ->
      ConjRel x F c Term.__eo_List_nil (mkForall (eoCons y zs) G)
  | unwrap {c G : Term} :
      ConjRel x F c Term.__eo_List_nil G ->
      ConjRel x F c Term.__eo_List_nil (mkForall Term.__eo_List_nil G)
  | final {cx g : Term} :
      substOne x cx F = g ->
      ConjRel x F cx Term.__eo_List_nil g

/-- Reified successful run of `__is_quant_dt_split x cs ys F G`. -/
inductive SplitRel (x ys F : Term) : Term -> Term -> Prop where
  | single {c g : Term} :
      ConjRel x F c ys g ->
      SplitRel x ys F (eoCons c Term.__eo_List_nil) g
  | nil_true :
      SplitRel x ys F Term.__eo_List_nil (Term.Boolean true)
  | step {c cs g G : Term} :
      ConjRel x F c ys g ->
      SplitRel x ys F cs G ->
      SplitRel x ys F (eoCons c cs) (mkAnd g G)

/-! ### Extraction from a successful guard run -/

private theorem conjRel_extract_aux (x F : Term) :
    ∀ n : Nat, ∀ c ys g : Term, sizeOf g < n ->
      (__eo_l_1___is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
        ConjRel x F c ys g) ∧
      (__is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
        ConjRel x F c ys g) := by
  intro n
  induction n with
  | zero => intro c ys g hsz; omega
  | succ n ih =>
      intro c ys g hsz
      have hl1 : __eo_l_1___is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
          ConjRel x F c ys g := by
        intro h
        fun_cases __eo_l_1___is_quant_dt_split_conj x c ys F g
        case case1 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case2 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case3 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case4 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        -- absorb arm
        case case5 =>
          rename_i y zs G _ _ _
          simp only [__eo_l_1___is_quant_dt_split_conj] at h
          obtain ⟨hFind, _, hRest⟩ := eo_requires_boolean_true_elim h
          obtain ⟨hFree, _, hRec⟩ := eo_requires_boolean_true_elim hRest
          refine ConjRel.absorb hFind hFree
            ((ih (Term.Apply c y) Term.__eo_List_nil (mkForall zs G) ?_).2 hRec)
          simp only [mkForall, eoCons] at hsz ⊢
          simp +arith at hsz ⊢
          omega
        -- unwrap arm
        case case6 =>
          rename_i G _ _ _
          simp only [__eo_l_1___is_quant_dt_split_conj] at h
          refine ConjRel.unwrap ((ih c Term.__eo_List_nil G ?_).2 h)
          simp +arith [mkForall] at hsz
          omega
        -- final arm
        case case7 =>
          have hred : __eo_l_1___is_quant_dt_split_conj x c Term.__eo_List_nil F g =
              __eo_eq (substOne x c F) g := by
            simp_all [__eo_l_1___is_quant_dt_split_conj, substOne]
          rw [hred] at h
          exact ConjRel.final (eo_eq_boolean_true_elim h)
        case case8 =>
          simp [__eo_l_1___is_quant_dt_split_conj] at h
      refine ⟨hl1, ?_⟩
      intro h
      fun_cases __is_quant_dt_split_conj x c ys F g
      case case1 => simp [__is_quant_dt_split_conj] at h
      case case2 => simp [__is_quant_dt_split_conj] at h
      case case3 => simp [__is_quant_dt_split_conj] at h
      case case4 => simp [__is_quant_dt_split_conj] at h
      case case5 => simp [__is_quant_dt_split_conj] at h
      -- the peel/ite arm
      case case6 =>
        rename_i y ys' y2 zs G _ _ _
        simp only [__is_quant_dt_split_conj] at h
        rcases eo_ite_boolean_true_elim h with ⟨hEq, hThen⟩ | ⟨_, hElse⟩
        · have hy : y = y2 := eo_eq_boolean_true_elim hEq
          subst hy
          obtain ⟨hFind, _, hRec⟩ := eo_requires_boolean_true_elim hThen
          refine ConjRel.peel hFind ((ih c ys' (mkForall zs G) ?_).2 hRec)
          simp only [mkForall, eoCons] at hsz ⊢
          simp +arith at hsz ⊢
          omega
        · exact hl1 hElse
      -- the fallback arm
      case case7 =>
        have hred : __is_quant_dt_split_conj x c ys F g =
            __eo_l_1___is_quant_dt_split_conj x c ys F g := by
          simp_all [__is_quant_dt_split_conj]
        rw [hred] at h
        exact hl1 h

theorem conjRel_of_guard_true (x F c ys g : Term)
    (h : __is_quant_dt_split_conj x c ys F g = Term.Boolean true) :
    ConjRel x F c ys g :=
  (conjRel_extract_aux x F (sizeOf g + 1) c ys g (by omega)).2 h

theorem splitRel_of_guard_true (x ys F : Term) :
    ∀ (cs G : Term),
      __is_quant_dt_split x cs ys F G = Term.Boolean true ->
      SplitRel x ys F cs G := by
  intro cs G h
  fun_cases __is_quant_dt_split x cs ys F G
  case case1 => simp [__is_quant_dt_split] at h
  case case2 => simp [__is_quant_dt_split] at h
  case case3 => simp [__is_quant_dt_split] at h
  case case4 => simp [__is_quant_dt_split] at h
  -- and-chain arm
  case case5 =>
    rename_i c' cs' g' G' _ _ _
    simp only [__is_quant_dt_split] at h
    obtain ⟨hConj, _, hRec⟩ := eo_requires_boolean_true_elim h
    exact SplitRel.step (conjRel_of_guard_true x F c' ys g' hConj)
      (splitRel_of_guard_true x ys F cs' G' hRec)
  -- nil/true arm
  case case6 =>
    exact SplitRel.nil_true
  -- singleton arm
  case case7 =>
    rename_i c' cs' _ _ _ _ _
    have hred : __is_quant_dt_split x (eoCons c' cs') ys F G =
        __eo_requires cs' Term.__eo_List_nil
          (__is_quant_dt_split_conj x c' ys F G) := by
      simp_all [__is_quant_dt_split]
    rw [hred] at h
    obtain ⟨hNil, _, hConj⟩ := eo_requires_boolean_true_elim h
    subst hNil
    exact SplitRel.single (conjRel_of_guard_true x F c' ys G hConj)
  case case8 =>
    simp [__is_quant_dt_split] at h

end QuantDtSplitRule

namespace QuantDtSplitRule

open InstantiateRule

set_option maxHeartbeats 4000000

/-! ## Semantic core (statements; proofs are the remaining work)

PROOF PLAN for `split_forward` / `split_backward` (see also the session notes in
the repository memory):

Vocabulary. Work through `smtForallEnc zs B := SmtTerm.not (__eo_to_smt_exists
zs (SmtTerm.not B))`, never through `__eo_to_smt` of virtual `mkForall zs G`
terms (the nil-binder case translates to `SmtTerm.None`).  A single-binder
step-iff (`eval M (not (exists s T tail)) = true ↔ ∀ v typed-canonical, eval
(push M s T v) (not tail) = true`, with `not tail` again an encoding) drives
the per-binder recursion; it is the one-step form of
`forall_encoding_true_iff` above.

Forward.  Characterize the LHS with `forall_encoding_true_iff`, then bridge to
"x pushed last": from `∀ N, Inst M (x::ys) N → eval N F̂ = true` derive
`H(M₀, ysRem) := ∀ N, Inst M₀ ysRem N → ∀ v typed-canonical at D̂, eval (push N
xkey v) F̂ = true` by induction over the `Inst` chain using push-reordering
(function-update equalities: `push_comm` for distinct keys, `push_same` for
equal keys — cf. the private lemmas in `Quant_var_reordering.lean:113,138`);
the x∈ys collision resolves because pushing the colliding retained binder with
`v` yields the same model function.  Then induct on `ConjRel`: `peel` consumes
a binder via step-iff and specializes `H`; `absorb` consumes a constructor-arg
binder (its key is insensitive for F̂ by the guard's freshness check, via
`smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped`);
`unwrap` is double-negation elimination (typing threaded via
`smtx_typeof_exists_tail_bool_of_cons_bool`); at `final`, rewrite with
`InstantiateRule.substitute_simul_eval` (actuals: the single binder x mapped to
the built constructor application cx) and instantiate `H` at `v := eval ĉx`,
which is typed-canonical by the spine lemmas plus the occurrence-typing
inversion below.

Backward.  Intro an LHS instantiation `N`; extract its push list; let `veff` be
the final value at x's key (handles x∈ys); decompose `veff` with
`datatype_value_spine`; the constructor index picks the conjunct out of
`SplitRel` (the guard consumed `__dt_get_constructors` in order, so the i-th
conjunct's seed is `Term.DtCons s d i` — correspondence via
`__eo_datatype_constructors_rec`); instantiate that conjunct's binders with the
retained values and the spine arguments (typed correctly by occurrence-typing);
at `final`, `substitute_simul_eval` gives `eval (push M₂ xkey veff) F̂ = true`
and the model equals `N` up to constructor-arg keys (insensitive) and push
order.

Occurrence-typing inversion (the largest remaining piece): if x occurs free in
F and `__smtx_typeof (__eo_to_smt (substOne x cx F)) ≠ SmtType.None` then
`__smtx_typeof (__eo_to_smt cx) ≠ SmtType.None`; together with the computed
`DtcAppType` chain of `SmtTerm.DtCons` this forces each absorbed binder type to
equal the corresponding (substituted) selector type and the result type to be
`D̂`.  When x is NOT free in F, `substOne x cx F = F` and both directions avoid
the spine entirely: F̂ is insensitive to the constructor-arg keys and to x's
key, and a typed-canonical witness for instantiating comes from
`model_total_typed` lookups (every well-formed type is inhabited in M).

Both directions case on `__contains_atomic_term_list_free_rec F [x] nil`.
-/

/-- The equality formula concluded by the rule. -/
abbrev qdsFormula (x ys F G : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (mkForall (eoCons x ys) F)) G

/--
Forward direction: if the left-hand universal is true, every conjunct produced
by a successful guard run is true.
-/
theorem split_forward
    (M : SmtModel) (hM : model_total_typed M)
    (x ys F G : Term)
    (srel : SplitRel x ys F (__dt_get_constructors (__eo_typeof x)) G)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool)
    (hLHS : __smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  sorry

/--
Backward direction: if the conjunction produced by a successful guard run is
true, the left-hand universal is true.
-/
theorem split_backward
    (M : SmtModel) (hM : model_total_typed M)
    (x ys F G : Term)
    (srel : SplitRel x ys F (__dt_get_constructors (__eo_typeof x)) G)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool)
    (hRHS : __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtValue.Boolean true := by
  sorry

/-! ## Assembly -/

theorem eo_to_smt_qds_eq (x ys F G : Term) :
    __eo_to_smt (qdsFormula x ys F G) =
      SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G) := by
  rfl

theorem smtx_typeof_eq_bool_elim
    {L R : SmtTerm}
    (hTy : __smtx_typeof (SmtTerm.eq L R) = SmtType.Bool) :
    __smtx_typeof L = __smtx_typeof R := by
  rw [show __smtx_typeof (SmtTerm.eq L R) =
    __smtx_typeof_eq (__smtx_typeof L) (__smtx_typeof R) from by
      simp only [__smtx_typeof]] at hTy
  rw [__smtx_typeof_eq] at hTy
  by_cases hEq : native_Teq (__smtx_typeof L) (__smtx_typeof R) = true
  · simpa [native_Teq] using hEq
  · exfalso
    have hf : native_Teq (__smtx_typeof L) (__smtx_typeof R) = false := by
      cases hv : native_Teq (__smtx_typeof L) (__smtx_typeof R)
      · rfl
      · exact absurd hv hEq
    rw [hf] at hTy
    simp only [native_ite, if_false] at hTy
    rw [__smtx_typeof_guard] at hTy
    by_cases hN : native_Teq (__smtx_typeof L) SmtType.None = true
    · rw [hN] at hTy
      simp [native_ite] at hTy
    · have hNf : native_Teq (__smtx_typeof L) SmtType.None = false := by
        cases hv : native_Teq (__smtx_typeof L) SmtType.None
        · rfl
        · exact absurd hv hN
      rw [hNf] at hTy
      simp [native_ite] at hTy

theorem smtx_typeof_eq_bool_left_ne_none
    {L R : SmtTerm}
    (hTy : __smtx_typeof (SmtTerm.eq L R) = SmtType.Bool) :
    __smtx_typeof L ≠ SmtType.None := by
  intro hN
  rw [show __smtx_typeof (SmtTerm.eq L R) =
    __smtx_typeof_eq (__smtx_typeof L) (__smtx_typeof R) from by
      simp only [__smtx_typeof]] at hTy
  rw [__smtx_typeof_eq, __smtx_typeof_guard, hN] at hTy
  simp [native_ite, native_Teq] at hTy

theorem smtx_typeof_not_bool_or_none (X : SmtTerm) :
    __smtx_typeof (SmtTerm.not X) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.not X) = SmtType.None := by
  rw [show __smtx_typeof (SmtTerm.not X) =
    native_ite (native_Teq (__smtx_typeof X) SmtType.Bool) SmtType.Bool SmtType.None from by
      simp only [__smtx_typeof]]
  by_cases h : native_Teq (__smtx_typeof X) SmtType.Bool = true
  · rw [h]; left; rfl
  · have hf : native_Teq (__smtx_typeof X) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof X) SmtType.Bool
      · rfl
      · exact absurd hv h
    rw [hf]; right; rfl

/--
Truth of the concluded equality, from a successful guard run.  This is the
target consumed by `Cpc/Proofs/Rules/Quant_dt_split.lean`.
-/
theorem qds_formula_true
    (M : SmtModel) (hM : model_total_typed M)
    (x ys F G : Term)
    (hGuard : __is_quant_dt_split x (__dt_get_constructors (__eo_typeof x)) ys F G =
      Term.Boolean true)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool) :
    eo_interprets M (qdsFormula x ys F G) true := by
  have srel : SplitRel x ys F (__dt_get_constructors (__eo_typeof x)) G :=
    splitRel_of_guard_true x ys F _ G hGuard
  -- SMT-side typing of the equality
  have hSmtBool : RuleProofs.eo_has_bool_type (qdsFormula x ys F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTrans hTy
  rw [RuleProofs.eo_has_bool_type] at hSmtBool
  rw [eo_to_smt_qds_eq] at hSmtBool
  -- both sides evaluate to Booleans
  have hLTy : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) = SmtType.Bool := by
    have hNe : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) ≠ SmtType.None :=
      smtx_typeof_eq_bool_left_ne_none hSmtBool
    have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
        SmtTerm.not (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
      SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil (eoCons x ys) F (by intro h; cases h)
    rw [hForm] at hNe ⊢
    rcases smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) with hB | hN
    · exact hB
    · exact absurd hN hNe
  have hRTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
    rw [← smtx_typeof_eq_bool_elim hSmtBool]
    exact hLTy
  obtain ⟨bL, hbL⟩ :=
    smt_model_eval_bool_is_boolean M hM _ hLTy
  obtain ⟨bR, hbR⟩ :=
    smt_model_eval_bool_is_boolean M hM _ hRTy
  -- the two sides agree
  have hAgree : bL = bR := by
    cases bL
    · cases bR
      · rfl
      · exfalso
        have := split_backward M hM x ys F G srel hTrans hTy hbR
        rw [hbL] at this
        exact absurd this (by decide)
    · cases bR
      · exfalso
        have := split_forward M hM x ys F G srel hTrans hTy hbL
        rw [hbR] at this
        exact absurd this (by decide)
      · rfl
  -- conclude the equality evaluates to true
  rw [eo_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · rw [eo_to_smt_qds_eq]; exact hSmtBool
  · rw [eo_to_smt_qds_eq]
    rw [show __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G)) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)))
        (__smtx_model_eval M (__eo_to_smt G)) from by
        simp only [__smtx_model_eval]]
    rw [hbL, hbR, hAgree]
    simp [__smtx_model_eval_eq, native_veq]

end QuantDtSplitRule
