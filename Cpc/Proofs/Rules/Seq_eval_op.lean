import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem seq_eval_op_shape {t u : Term}
    (h :
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠
        Term.Stuck) :
    __seq_eval t = u ∧
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u := by
  change __eo_requires (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠ Term.Stuck at h
  exact ⟨eo_requires_eq_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h,
    eo_requires_eq_result_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h⟩

private theorem term_ne_stuck_of_eo_is_list_true (f x : Term)
    (h : __eo_is_list f x = Term.Boolean true) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_is_list] at h

private theorem eo_list_concat_str_concat_lists_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hA := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hZ := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  exact ⟨hA, hZ⟩

private theorem eo_list_concat_str_concat_eq_rec_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hOuter := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInner := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hOuter, hInner]

private theorem str_value_len_numeral_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    ∃ n : native_Int, __str_value_len x = Term.Numeral n := by
  induction x using __str_value_len.induct with
  | case1 =>
      simp [__str_value_len] at h
  | case2 e ss ih =>
      change __eo_add (Term.Numeral 1) (__str_value_len ss) ≠ Term.Stuck at h
      have hTailNe : __str_value_len ss ≠ Term.Stuck := by
        intro hTail
        rw [hTail] at h
        simp [__eo_add] at h
      rcases ih hTailNe with ⟨n, hn⟩
      change ∃ m : native_Int,
        __eo_add (Term.Numeral 1) (__str_value_len ss) = Term.Numeral m
      rw [hn]
      simp [__eo_add, native_zplus]
  | case3 T =>
      exact ⟨0, by simp [__str_value_len]⟩
  | case4 e =>
      exact ⟨1, by simp [__str_value_len]⟩
  | case5 s hs1 hs2 hs3 =>
      cases s <;>
        simp [__str_value_len, __eo_requires, __eo_is_str,
          __eo_is_str_internal, __eo_len, native_ite, native_teq,
          SmtEval.native_and, SmtEval.native_not] at h ⊢

private theorem str_value_len_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_value_len] at h

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem smt_typeof_seq_value_of_eval_seq
    (M : SmtModel) (hM : model_total_typed M)
    (t : Term) (T : SmtType) (sx : SmtSeq)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq sx) :
    __smtx_typeof_seq_value sx = SmtType.Seq T := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by
        unfold term_has_non_none_type
        rw [hTy]
        exact seq_ne_none T)
  rw [hEval] at hEvalTy
  simpa [__smtx_typeof_value, hTy] using hEvalTy

private theorem str_len_int_eval_of_seq_eval
    (M : SmtModel) (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
  intro hSEval
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length)
  rw [smtx_eval_str_len_term_eq, hSEval]
  simp [__smtx_model_eval_str_len, native_seq_len]

private theorem smt_value_rel_model_eval_str_len_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_len a) (__smtx_model_eval_str_len b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_len, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_contains_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_contains a b)
      (__smtx_model_eval_str_contains c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    unfold RuleProofs.smt_value_rel
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
        native_veq]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      unfold RuleProofs.smt_value_rel
      cases a <;>
        simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_prefixof_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_prefixof a b)
      (__smtx_model_eval_str_prefixof c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    unfold RuleProofs.smt_value_rel
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
        __smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      unfold RuleProofs.smt_value_rel
      cases a <;>
        simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_substr,
          __smtx_model_eval_eq, native_veq]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_suffixof_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_suffixof a b)
      (__smtx_model_eval_str_suffixof c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    unfold RuleProofs.smt_value_rel
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
        __smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      unfold RuleProofs.smt_value_rel
      cases a <;>
        simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_substr,
          __smtx_model_eval_eq, native_veq]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

private theorem native_seq_prefix_eq_take_eq_true
    (xs ys : List SmtValue)
    (h : ys.take xs.length = xs) :
    native_seq_prefix_eq xs ys = true := by
  rw [RuleProofs.native_seq_prefix_eq_iff]
  exact ⟨ys.drop xs.length, by
    calc
      ys = ys.take xs.length ++ ys.drop xs.length :=
        (List.take_append_drop xs.length ys).symm
      _ = xs ++ ys.drop xs.length := by rw [h]⟩

private theorem native_seq_prefix_eq_append_left_same
    (pre xs ys : List SmtValue) :
    native_seq_prefix_eq (pre ++ xs) (pre ++ ys) =
      native_seq_prefix_eq xs ys := by
  induction pre with
  | nil => rfl
  | cons p ps ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_prefix_eq_cons_nil_false
    (x : SmtValue) (xs : List SmtValue) :
    native_seq_prefix_eq (x :: xs) [] = false := by
  rfl

private theorem native_seq_prefix_eq_cons_cons_false_of_veq_false
    {x y : SmtValue} {xs ys : List SmtValue}
    (h : native_veq x y = false) :
    native_seq_prefix_eq (x :: xs) (y :: ys) = false := by
  simp [native_seq_prefix_eq, h]

private theorem native_veq_false_of_model_eval_eq_false_char
    {x y : SmtValue}
    (hx : __smtx_typeof_value x = SmtType.Char)
    (hy : __smtx_typeof_value y = SmtType.Char)
    (h : __smtx_model_eval_eq x y = SmtValue.Boolean false) :
    native_veq x y = false := by
  cases x <;> cases y <;>
    simp [__smtx_typeof_value, __smtx_model_eval_eq, native_veq] at hx hy h ⊢
  all_goals assumption

private theorem seq_is_prefix_left_ne_stuck_of_ne_stuck (a b : Term)
    (h : __seq_is_prefix a b ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  simp [__seq_is_prefix] at h

private theorem seq_is_prefix_right_ne_stuck_of_ne_stuck (a b : Term)
    (h : __seq_is_prefix a b ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> simp [__seq_is_prefix] at h

private theorem seq_element_of_unit_eq_of_ne_stuck (x : Term)
    (h : __seq_element_of_unit x ≠ Term.Stuck) :
    ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e ∧
      __seq_element_of_unit x = e := by
  cases x <;> simp [__seq_element_of_unit] at h ⊢
  case Apply f e =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

private theorem eo_list_nth_eq_rec_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_list_nth f a n = __eo_list_nth_rec a n := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_eq_result_of_ne_stuck (__eo_is_list f a)
    (Term.Boolean true) (__eo_list_nth_rec a n) h

private theorem eo_list_nth_is_list_true_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_is_list f a = Term.Boolean true := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_nth_rec a n) h

private theorem eo_list_nth_rec_ne_stuck_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_list_nth_rec a n ≠ Term.Stuck := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a)
    (Term.Boolean true) (__eo_list_nth_rec a n) h

private theorem eo_is_list_str_concat_cons_fun_eq (g x y : Term)
    (h :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) =
        Term.Boolean true) :
    g = Term.UOp UserOp.str_concat := by
  cases g <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
      __eo_is_ok, native_teq, native_ite, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp at h ⊢

private theorem smt_typeof_list_nth_rec_str_concat_of_seq :
    ∀ a n T,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __eo_list_nth_rec a n ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_list_nth_rec a n)) =
        SmtType.Seq T := by
  intro a n
  induction a, n using __eo_list_nth_rec.induct with
  | case1 n =>
      intro T _hList _hTy hNe
      simp [__eo_list_nth_rec] at hNe
  | case2 f x y =>
      intro T hList hTy _hNe
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      exact (strConcat_args_of_seq_type x y T
        (by simpa [mkConcat] using hTy)).1
  | case3 f x y n _hnStuck hnZero ih =>
      intro T hList hTy hNe
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          x y (by simpa [mkConcat] using hList)
      have hTailTy :
          __smtx_typeof (__eo_to_smt y) = SmtType.Seq T :=
        (strConcat_args_of_seq_type x y T
          (by simpa [mkConcat] using hTy)).2
      have hTailNe :
          __eo_list_nth_rec y (__eo_add n (Term.Numeral (-1 : native_Int))) ≠
            Term.Stuck := by
        simpa [__eo_list_nth_rec, hnZero] using hNe
      simpa [__eo_list_nth_rec, hnZero] using
        ih T hTailList hTailTy hTailNe
  | case4 t x hxStuck hNotZero hNotCons =>
      intro T hList hTy hNe
      simp [__eo_list_nth_rec] at hNe

private theorem smt_value_rel_seq_nth_left_congr
    (M : SmtModel) (hM : model_total_typed M)
    (x y n : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))) :
    RuleProofs.smt_value_rel
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt n)))
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt n))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hnValTy := smt_model_eval_preserves_type M hM (__eo_to_smt n)
    SmtType.Int hnTy (by simp) type_inhabited_int
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases int_value_canonical hnValTy with ⟨i, hnEval⟩
  have hSeqEq : sx = sy := by
    unfold RuleProofs.smt_value_rel at hRel
    rw [hxEval, hyEval] at hRel
    simpa [__smtx_model_eval_eq, native_veq] using hRel
  subst sy
  rw [hxEval, hyEval, hnEval]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_seq_nth M (SmtValue.Seq sx) (SmtValue.Numeral i))

private theorem smtx_model_eval_seq_unit_term (M : SmtModel) (e : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
          (SmtSeq.empty
            (__smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt e))))) := by
  change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
    SmtValue.Seq
      (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
        (SmtSeq.empty
          (__smtx_typeof_value
            (__smtx_model_eval M (__eo_to_smt e)))))
  simp [__smtx_model_eval]

private theorem smtx_model_eval_seq_nth_term
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_nth x y) =
      __smtx_seq_nth M (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem str_value_len_concat_head_seq_unit (x y : Term)
    (h : __str_value_len (mkConcat x y) ≠ Term.Stuck) :
    ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e := by
  rcases str_value_len_numeral_of_ne_stuck (mkConcat x y) h with ⟨n, hn⟩
  rcases RuleProofs.value_len_numeral_cases (mkConcat x y) n hn with
      ⟨w, hw⟩ | ⟨e, ss, hcons⟩ | ⟨U, hU⟩ | ⟨e, hUnit⟩
  · cases hw
  · injection hcons with hx _hy
    injection hx with _ hx'
    exact ⟨e, hx'⟩
  · cases hU
  · cases hUnit

private theorem str_value_len_concat_tail_ne_stuck (e tail : Term)
    (h :
      __str_value_len
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ≠
        Term.Stuck) :
    __str_value_len tail ≠ Term.Stuck := by
  intro hTail
  change __eo_add (Term.Numeral 1) (__str_value_len tail) ≠
    Term.Stuck at h
  rw [hTail] at h
  simp [__eo_add] at h

private theorem smt_value_rel_list_nth_rec_ssm_of_value_len
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ a n e T sx i d,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __str_value_len a ≠ Term.Stuck ->
      __eo_list_nth_rec a n = Term.Apply (Term.UOp UserOp.seq_unit) e ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral i ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt e))
        (__smtx_ssm_seq_nth sx i d) := by
  intro a n
  induction a, n using __eo_list_nth_rec.induct with
  | case1 n =>
      intro e T sx i d _hList _hTy _hLen hNth _hEvalA _hEvalN
      simp [__eo_list_nth_rec] at hNth
  | case2 f x y =>
      intro e T sx i d hList hTy _hLen hNth hEvalA hEvalN
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      have hx : x = Term.Apply (Term.UOp UserOp.seq_unit) e := by
        simpa [__eo_list_nth_rec] using hNth
      subst x
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type (Term.Apply (Term.UOp UserOp.seq_unit) e)
          y T (by simpa [mkConcat] using hTy)
      rcases seq_eval_of_seq_type M hM y T hTailTy with ⟨sy, hTailEval⟩
      have hsx :
          sx =
            native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e)))
              (__smtx_model_eval M (__eo_to_smt e) ::
                native_unpack_seq sy) := by
        rw [smtx_model_eval_str_concat_term_eq, hTailEval] at hEvalA
        rw [smtx_model_eval_seq_unit_term] at hEvalA
        simp [__smtx_model_eval_str_concat, native_seq_concat,
          native_unpack_seq, __smtx_elem_typeof_seq_value] at hEvalA
        exact hEvalA.symm
      change __smtx_model_eval M (SmtTerm.Numeral 0) =
        SmtValue.Numeral i at hEvalN
      rw [__smtx_model_eval.eq_2] at hEvalN
      injection hEvalN with hi
      subst i
      rw [hsx]
      simp [__smtx_ssm_seq_nth, native_pack_seq,
        RuleProofs.smt_value_rel_refl]
  | case3 f x y n _hnStuck hnZero ih =>
      intro e T sx i d hList hTy hLen hNth hEvalA hEvalN
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      rcases str_value_len_concat_head_seq_unit x y
          (by simpa [mkConcat] using hLen) with ⟨e0, hx⟩
      subst x
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y
          (by simpa [mkConcat] using hList)
      have hTailTy :
          __smtx_typeof (__eo_to_smt y) = SmtType.Seq T :=
        (strConcat_args_of_seq_type
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y T
          (by simpa [mkConcat] using hTy)).2
      have hTailLen : __str_value_len y ≠ Term.Stuck :=
        str_value_len_concat_tail_ne_stuck e0 y
          (by simpa [mkConcat] using hLen)
      have hTailNth :
          __eo_list_nth_rec y (__eo_add n (Term.Numeral (-1 : native_Int))) =
            Term.Apply (Term.UOp UserOp.seq_unit) e := by
        simpa [__eo_list_nth_rec, hnZero] using hNth
      rcases seq_eval_of_seq_type M hM y T hTailTy with ⟨sy, hTailEval⟩
      have hTailSeqTy :
          __smtx_typeof_seq_value sy = SmtType.Seq T :=
        smt_typeof_seq_value_of_eval_seq M hM y T sy hTailTy hTailEval
      have hTailElem : __smtx_elem_typeof_seq_value sy = T :=
        elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
      have hHeadTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e0)) =
            SmtType.Seq T :=
        (strConcat_args_of_seq_type
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y T
          (by simpa [mkConcat] using hTy)).1
      have hE0TyInfo :=
        seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e0) (A := T) hHeadTy
      have hE0ValTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt e0)) = T := by
        have hE0NN : term_has_non_none_type (__eo_to_smt e0) := by
          unfold term_has_non_none_type
          rw [hE0TyInfo.1]
          exact hE0TyInfo.2
        exact (smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt e0) hE0NN).trans hE0TyInfo.1
      have hPackTail :
          native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e0)))
              (native_unpack_seq sy) =
            sy := by
        rw [hE0ValTy]
        simpa [hTailElem] using native_pack_unpack_seq sy
      have hsx :
          sx =
            native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e0)))
              (__smtx_model_eval M (__eo_to_smt e0) ::
                native_unpack_seq sy) := by
        rw [smtx_model_eval_str_concat_term_eq, hTailEval] at hEvalA
        rw [smtx_model_eval_seq_unit_term] at hEvalA
        simp [__smtx_model_eval_str_concat, native_seq_concat,
          native_unpack_seq, __smtx_elem_typeof_seq_value] at hEvalA
        exact hEvalA.symm
      cases n <;>
        simp [__eo_add, __eo_list_nth_rec] at hTailNth hEvalN
      case Numeral j =>
        change __smtx_model_eval M (SmtTerm.Numeral j) =
          SmtValue.Numeral i at hEvalN
        rw [__smtx_model_eval.eq_2] at hEvalN
        injection hEvalN with hji
        subst i
        have hj0 : j ≠ 0 := by
          intro hj
          apply hnZero
          subst j
          rfl
        have hPredEval :
            __smtx_model_eval M
                (__eo_to_smt (__eo_add (Term.Numeral j)
                  (Term.Numeral (-1 : native_Int)))) =
              SmtValue.Numeral (native_zplus j (native_zneg 1)) := by
          change __smtx_model_eval M
              (SmtTerm.Numeral (native_zplus j (-1 : native_Int))) =
            SmtValue.Numeral (native_zplus j (native_zneg 1))
          rw [__smtx_model_eval.eq_2]
          rfl
        have hTailRel :=
          ih e T sy (native_zplus j (native_zneg 1)) d hTailList hTailTy
            hTailLen hTailNth hTailEval hPredEval
        rw [hsx]
        simpa [__smtx_ssm_seq_nth, native_pack_seq, hPackTail, hj0] using
          hTailRel
  | case4 t x hxStuck hNotZero hNotCons =>
      intro e T sx i d hList hTy hLen hNth hEvalA hEvalN
      simp [__eo_list_nth_rec] at hNth

private theorem smt_value_rel_seq_nth_list_rec_of_value_len
    (M : SmtModel) (hM : model_total_typed M)
    (a n e : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hLen : __str_value_len a ≠ Term.Stuck)
    (hNth :
      __eo_list_nth_rec a n = Term.Apply (Term.UOp UserOp.seq_unit) e)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt e))
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt n))) := by
  have haValTy := smt_model_eval_preserves_type M hM (__eo_to_smt a)
    (SmtType.Seq T) hTy (seq_ne_none T) (type_inhabited_seq T)
  have hnValTy := smt_model_eval_preserves_type M hM (__eo_to_smt n)
    SmtType.Int hnTy (by simp) type_inhabited_int
  rcases seq_value_canonical haValTy with ⟨sx, haEval⟩
  rcases int_value_canonical hnValTy with ⟨i, hnEval⟩
  rw [haEval, hnEval]
  simp [__smtx_seq_nth]
  exact smt_value_rel_list_nth_rec_ssm_of_value_len M hM a n e T sx i
    (__smtx_seq_nth_wrong M sx i (__smtx_typeof_seq_value sx))
    hList hTy hLen hNth haEval hnEval

private theorem seq_element_list_nth_seq_empty_stuck
    (U n : Term) :
    __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U)) n) =
      Term.Stuck := by
  cases n <;>
    simp [__eo_list_nth, __eo_list_nth_rec, __eo_requires,
      __eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __seq_element_of_unit, native_teq,
      native_ite, SmtEval.native_not]

private theorem seq_element_list_nth_explicit_char_empty_cons_stuck
    (n : Term) :
    __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))))
            (Term.String [])) n) =
      Term.Stuck := by
  cases n <;>
    simp [__eo_list_nth, __eo_list_nth_rec, __eo_requires, __eo_add,
      __eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __seq_element_of_unit, __eo_eq,
      native_teq, native_ite, SmtEval.native_not]
  case Numeral i =>
    by_cases hi : i = 0 <;>
      simp [__eo_list_nth_rec, __eo_add, hi]

private theorem seq_element_list_nth_intro_seq_empty_stuck
    (U n : Term) :
    __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (__str_nary_intro
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) U))) n) =
      Term.Stuck := by
  by_cases hChar : U = Term.UOp UserOp.Char
  · subst U
    let emp :=
      Term.UOp1 UserOp1.seq_empty
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    have hEmpty : __seq_empty (__eo_typeof emp) = Term.String [] := by
      rw [RuleProofs.explicitCharEmpty_typeof]
      rfl
    have hIntro :
        __str_nary_intro emp =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) emp)
            (Term.String []) := by
      change __eo_ite (__eo_eq emp (__seq_empty (__eo_typeof emp))) emp
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) emp)
            (__seq_empty (__eo_typeof emp))) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) emp)
          (Term.String [])
      rw [hEmpty]
      simp [__eo_eq, __eo_mk_apply, native_teq, native_ite]
    change __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (__str_nary_intro emp) n) =
      Term.Stuck
    rw [hIntro]
    exact seq_element_list_nth_explicit_char_empty_cons_stuck n
  · let emp :=
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    by_cases hUType : __eo_typeof U = Term.Type
    · have hEmpTy : __eo_typeof emp = Term.Apply (Term.UOp UserOp.Seq) U := by
        change __eo_typeof_seq_empty
            (__eo_typeof_Seq (__eo_typeof U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.UOp UserOp.Seq) U
        rw [hUType]
        rfl
      have hEmpty : __seq_empty (__eo_typeof emp) = emp := by
        rw [hEmpTy]
        simp [emp, __seq_empty, hChar]
      have hIntro : __str_nary_intro emp = emp := by
        change __eo_ite (__eo_eq emp (__seq_empty (__eo_typeof emp))) emp
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) emp)
              (__seq_empty (__eo_typeof emp))) =
          emp
        rw [hEmpty]
        simp [__eo_eq, native_teq, native_ite]
      change __seq_element_of_unit
          (__eo_list_nth (Term.UOp UserOp.str_concat)
            (__str_nary_intro emp) n) =
        Term.Stuck
      rw [hIntro]
      exact seq_element_list_nth_seq_empty_stuck U n
    · have hSeqTy :
          __eo_typeof (Term.Apply (Term.UOp UserOp.Seq) U) = Term.Stuck := by
        change __eo_typeof_Seq (__eo_typeof U) = Term.Stuck
        cases hUTy : __eo_typeof U <;>
          simp [__eo_typeof_Seq, hUTy] at hUType ⊢
      have hEmpTy : __eo_typeof emp = Term.Stuck := by
        change __eo_typeof_seq_empty
            (__eo_typeof (Term.Apply (Term.UOp UserOp.Seq) U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Stuck
        rw [hSeqTy]
        rfl
      have hIntro : __str_nary_intro emp = Term.Stuck := by
        change __eo_ite (__eo_eq emp (__seq_empty (__eo_typeof emp))) emp
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) emp)
              (__seq_empty (__eo_typeof emp))) =
          Term.Stuck
        rw [hEmpTy]
        rfl
      change __seq_element_of_unit
          (__eo_list_nth (Term.UOp UserOp.str_concat)
            (__str_nary_intro emp) n) =
        Term.Stuck
      rw [hIntro]
      simp [__eo_list_nth, __eo_requires, __eo_is_list,
        __seq_element_of_unit, native_teq, native_ite]

private theorem seq_empty_uop1_unpack_nil_of_seq_char
    (M : SmtModel) (A : Term) (sx : SmtSeq)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq SmtType.Char)
    (hEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtValue.Seq sx) :
    native_unpack_seq sx = [] := by
  change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtType.Seq SmtType.Char at hTy
  change __smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtValue.Seq sx at hEval
  cases hA : __eo_to_smt_type A with
  | Seq U =>
      simp [__eo_to_smt_seq_empty, hA] at hTy hEval
      rw [smtx_typeof_seq_empty_term_eq] at hTy
      have hGuardNN :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) ≠
            SmtType.None := by
        rw [hTy]
        exact seq_ne_none SmtType.Char
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) =
            SmtType.Seq U :=
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq U) (SmtType.Seq U)
          hGuardNN
      rw [hGuard] at hTy
      injection hTy with hU
      subst U
      rw [smtx_eval_seq_empty_term_eq] at hEval
      injection hEval with hSx
      subst sx
      rfl
  | _ =>
      simp [__eo_to_smt_seq_empty, hA, TranslationProofs.smtx_typeof_none]
        at hTy

private theorem seq_unit_concat_unpack_cons_char
    (M : SmtModel) (hM : model_total_typed M)
    (e tail : Term) (sx : SmtSeq)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtType.Seq SmtType.Char)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtValue.Seq sx) :
    ∃ rest,
      native_unpack_seq sx =
        __smtx_model_eval M (__eo_to_smt e) :: rest ∧
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) =
        SmtType.Char := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  obtain ⟨hHeadTy, hTailTy⟩ :=
    strConcat_args_of_seq_type head tail SmtType.Char
      (by simpa [head] using hTy)
  rcases seq_eval_of_seq_type M hM tail SmtType.Char hTailTy with
    ⟨stail, hTailEval⟩
  let shead :=
    SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
      (SmtSeq.empty
        (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e))))
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt head) = SmtValue.Seq shead := by
    change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq shead
    simp [__smtx_model_eval, shead]
  have hHeadUnp :
      native_unpack_seq shead =
        [__smtx_model_eval M (__eo_to_smt e)] := by
    simp [shead, native_unpack_seq]
  obtain ⟨sxy, hWholeEval, hWholeUnp⟩ :=
    RuleProofs.strConcat_unpack_eval M head tail shead stail
      hHeadEval hTailEval
  have hSx : sx = sxy := by
    rw [hEval] at hWholeEval
    injection hWholeEval
  have hElemTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) =
        SmtType.Char := by
    have hArgTy :
        __smtx_typeof (__eo_to_smt e) = SmtType.Char :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e)
        (A := SmtType.Char) (by simpa [head] using hHeadTy)).1
    have hPres := Smtm.smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt e)
      (by
        unfold term_has_non_none_type
        rw [hArgTy]
        intro h
        cases h)
    simpa [hArgTy] using hPres
  refine ⟨native_unpack_seq stail, ?_, hElemTy⟩
  rw [hSx, hWholeUnp, hHeadUnp]
  rfl

private theorem str_concat_unpack_of_seq_evals
    (M : SmtModel) (x y : Term) (sxy sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hxy : __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      SmtValue.Seq sxy) :
    native_unpack_seq sxy = native_unpack_seq sx ++ native_unpack_seq sy := by
  obtain ⟨sxy', hEval, hUnp⟩ :=
    RuleProofs.strConcat_unpack_eval M x y sx sy hx hy
  have hSeq : sxy = sxy' := by
    rw [hxy] at hEval
    injection hEval
  rw [hSeq]
  exact hUnp

private theorem seq_prefix_l2_eq_bool_native_char
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ a b sx sy,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_2___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_2___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy)) := by
  intro a b sx sy hATy hBTy hAEval hBEval hNe
  unfold __eo_l_2___seq_is_prefix at hNe ⊢
  split at hNe <;> simp at hNe ⊢
  case h_2 x1 x2 et ts es ss =>
    let guard :=
      __eo_ite (__eo_eq et es) (Term.Boolean false)
        (__are_distinct_terms_type et es (__eo_typeof et))
    have hOut :
        __eo_requires guard (Term.Boolean true) (Term.Boolean false) =
          Term.Boolean false :=
      eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true)
        (Term.Boolean false) (by simpa [guard] using hNe)
    have hGuard : guard = Term.Boolean true :=
      eo_requires_eq_of_ne_stuck guard (Term.Boolean true)
        (Term.Boolean false) (by simpa [guard] using hNe)
    rcases seq_unit_concat_unpack_cons_char M hM et ts sx
        (by simpa using hATy) (by simpa using hAEval) with
      ⟨restA, hUnpA, hEtTy⟩
    rcases seq_unit_concat_unpack_cons_char M hM es ss sy
        (by simpa using hBTy) (by simpa using hBEval) with
      ⟨restB, hUnpB, hEsTy⟩
    have hGuardParts :
        __eo_eq et es = Term.Boolean false ∧
          __are_distinct_terms_type et es (__eo_typeof et) =
            Term.Boolean true :=
      eo_ite_eq_false_guard_true (by simpa [guard] using hGuard)
    have hEqFalse : __eo_eq et es = Term.Boolean false := hGuardParts.1
    have hDistinct :
        __are_distinct_terms_type et es (__eo_typeof et) =
          Term.Boolean true := hGuardParts.2
    have hEtArgTy :
        __smtx_typeof (__eo_to_smt et) = SmtType.Char :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt et)
        (A := SmtType.Char)
        (by
          exact (strConcat_args_of_seq_type
            (Term.Apply (Term.UOp UserOp.seq_unit) et) ts
            SmtType.Char (by simpa using hATy)).1)).1
    have hEsArgTy :
        __smtx_typeof (__eo_to_smt es) = SmtType.Char :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt es)
        (A := SmtType.Char)
        (by
          exact (strConcat_args_of_seq_type
            (Term.Apply (Term.UOp UserOp.seq_unit) es) ss
            SmtType.Char (by simpa using hBTy)).1)).1
    have hEtTrans : RuleProofs.eo_has_smt_translation et := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hEtArgTy]
      intro h
      cases h
    have hEsTrans : RuleProofs.eo_has_smt_translation es := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hEsArgTy]
      intro h
      cases h
    have hEvalEqFalse :
        __smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt et))
            (__smtx_model_eval M (__eo_to_smt es)) =
          SmtValue.Boolean false :=
      are_distinct_terms_type_model_eval_eq_false M hM et es
        hEtTrans hEsTrans hEqFalse hDistinct
    have hVeqFalse :
        native_veq (__smtx_model_eval M (__eo_to_smt et))
            (__smtx_model_eval M (__eo_to_smt es)) = false :=
      native_veq_false_of_model_eval_eq_false_char hEtTy hEsTy
        hEvalEqFalse
    rw [hOut, hUnpA, hUnpB]
    rw [native_seq_prefix_eq_cons_cons_false_of_veq_false
      (xs := restA) (ys := restB) hVeqFalse]
  case h_3 =>
    have hNil :
        native_unpack_seq sx = [] :=
      seq_empty_uop1_unpack_nil_of_seq_char M _ sx hATy hAEval
    rw [hNil]
    rfl
  case h_4 =>
    rcases seq_unit_concat_unpack_cons_char M hM _ _ sx
        (by simpa using hATy) (by simpa using hAEval) with
      ⟨restA, hUnpA, _hEtTy⟩
    have hNil :
        native_unpack_seq sy = [] :=
      seq_empty_uop1_unpack_nil_of_seq_char M _ sy hBTy hBEval
    rw [hUnpA, hNil]
    rfl

private theorem seq_prefix_l1_eq_bool_native_char
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ a b sx sy,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_1___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_1___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy)) := by
  intro a b
  let motive1 : Term -> Term -> Prop := fun a b =>
    ∀ sx sy,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_1___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_1___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy))
  let motive2 : Term -> Term -> Prop := fun a b =>
    ∀ sx sy,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __seq_is_prefix a b ≠ Term.Stuck ->
      __seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy))
  change motive1 a b
  refine __eo_l_1___seq_is_prefix.induct motive1 motive2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
  · intro x
    dsimp [motive1]
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe
  · intro x hx
    dsimp [motive1]
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe
  · intro t t2 u s2 ih
    dsimp [motive1]
    dsimp [motive2] at ih
    intro sx sy hATy hBTy hAEval hBEval hNe
    let a := mkConcat t t2
    let b := mkConcat u s2
    let l2 := __eo_l_2___seq_is_prefix a b
    simp [__eo_l_1___seq_is_prefix] at hNe ⊢
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u)
        (__seq_is_prefix t2 s2) l2 hNe with hCond | hCond
    · have hTailNe : __seq_is_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hNe
      obtain ⟨hHeadTyA, hTailTyA⟩ :=
        strConcat_args_of_seq_type t t2 SmtType.Char hATy
      obtain ⟨_hHeadTyB, hTailTyB⟩ :=
        strConcat_args_of_seq_type u s2 SmtType.Char hBTy
      rcases seq_eval_of_seq_type M hM t SmtType.Char hHeadTyA with
        ⟨sHead, hHeadEvalA⟩
      rcases seq_eval_of_seq_type M hM t2 SmtType.Char hTailTyA with
        ⟨sTailA, hTailEvalA⟩
      rcases seq_eval_of_seq_type M hM s2 SmtType.Char hTailTyB with
        ⟨sTailB, hTailEvalB⟩
      have hHeadEq : u = t :=
        eq_of_eo_eq_true_local t u hCond
      have hHeadEvalB :
          __smtx_model_eval M (__eo_to_smt u) = SmtValue.Seq sHead := by
        simpa [hHeadEq] using hHeadEvalA
      have hUnpA :
          native_unpack_seq sx =
            native_unpack_seq sHead ++ native_unpack_seq sTailA :=
        str_concat_unpack_of_seq_evals M t t2 sx sHead sTailA
          hHeadEvalA hTailEvalA hAEval
      have hUnpB :
          native_unpack_seq sy =
            native_unpack_seq sHead ++ native_unpack_seq sTailB :=
        str_concat_unpack_of_seq_evals M u s2 sy sHead sTailB
          hHeadEvalB hTailEvalB hBEval
      have hTailEq :
          __seq_is_prefix t2 s2 =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sTailA)
                (native_unpack_seq sTailB)) :=
        ih sTailA sTailB hTailTyA hTailTyB
          hTailEvalA hTailEvalB hTailNe
      rw [hCond, eo_ite_true, hTailEq, hUnpA, hUnpB]
      rw [native_seq_prefix_eq_append_left_same]
    · have hL2Ne : l2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      have hL2Eq :
          l2 =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        seq_prefix_l2_eq_bool_native_char M hM a b sx sy
          hATy hBTy hAEval hBEval hL2Ne
      rw [hCond, eo_ite_false]
      simpa [l2, a, b] using hL2Eq
  · intro x y hx hy hNotBoth
    dsimp [motive1]
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe ⊢
    exact seq_prefix_l2_eq_bool_native_char M hM x y sx sy
      hATy hBTy hAEval hBEval hNe
  · intro x
    dsimp [motive2]
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__seq_is_prefix] at hNe
  · intro x hx
    dsimp [motive2]
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__seq_is_prefix] at hNe
  · intro x y hx hy ih
    dsimp [motive2]
    dsimp [motive1] at ih
    intro sx sy hATy hBTy hAEval hBEval hNe
    simp [__seq_is_prefix] at hNe ⊢
    rcases eo_ite_cases_of_ne_stuck (__eo_eq x y) (Term.Boolean true)
        (__eo_l_1___seq_is_prefix x y) hNe with hCond | hCond
    · have hXY : y = x :=
        eq_of_eo_eq_true_local x y hCond
      have hSeq : sx = sy := by
        rw [hXY, hAEval] at hBEval
        injection hBEval
      rw [hCond, eo_ite_true, hSeq]
      simp [native_seq_prefix_eq_self]
    · have hL1Ne : __eo_l_1___seq_is_prefix x y ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      have hL1Eq :
          __eo_l_1___seq_is_prefix x y =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        ih sx sy hATy hBTy hAEval hBEval hL1Ne
      rw [hCond, eo_ite_false, hL1Eq]

private theorem seq_prefix_eq_bool_native_char
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) (sx sy : SmtSeq)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy)
    (hNe : __seq_is_prefix a b ≠ Term.Stuck) :
    __seq_is_prefix a b =
      Term.Boolean
        (native_seq_prefix_eq (native_unpack_seq sx)
          (native_unpack_seq sy)) := by
  have hA : a ≠ Term.Stuck :=
    seq_is_prefix_left_ne_stuck_of_ne_stuck a b hNe
  have hB : b ≠ Term.Stuck :=
    seq_is_prefix_right_ne_stuck_of_ne_stuck a b hNe
  have hSeqDef :
      __seq_is_prefix a b =
        __eo_ite (__eo_eq a b) (Term.Boolean true)
          (__eo_l_1___seq_is_prefix a b) := by
    cases a <;> cases b <;> simp [__seq_is_prefix] at hA hB ⊢
  have hNeIte :
      __eo_ite (__eo_eq a b) (Term.Boolean true)
          (__eo_l_1___seq_is_prefix a b) ≠ Term.Stuck := by
    simpa [hSeqDef] using hNe
  rcases eo_ite_cases_of_ne_stuck (__eo_eq a b) (Term.Boolean true)
      (__eo_l_1___seq_is_prefix a b) hNeIte with hCond | hCond
  · have hBA : b = a :=
      eq_of_eo_eq_true_local a b hCond
    have hSeq : sx = sy := by
      rw [hBA, hAEval] at hBEval
      injection hBEval
    rw [hSeqDef, hCond, eo_ite_true, hSeq]
    simp [native_seq_prefix_eq_self]
  · have hL1Ne : __eo_l_1___seq_is_prefix a b ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hNeIte
    have hL1Eq :
        __eo_l_1___seq_is_prefix a b =
          Term.Boolean
            (native_seq_prefix_eq (native_unpack_seq sx)
              (native_unpack_seq sy)) :=
      seq_prefix_l1_eq_bool_native_char M hM a b sx sy
        hATy hBTy hAEval hBEval hL1Ne
    rw [hSeqDef, hCond, eo_ite_false, hL1Eq]

private theorem native_seq_extract_zero_nat_any
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n <= xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length <= n := Nat.le_of_lt hLenLt
        have hLenNotLe :
            ¬ ((Int.ofNat xs.length : Int) + 1 <= 0) := by
          have hNonneg : (0 : Int) <= Int.ofNat xs.length :=
            Int.natCast_nonneg xs.length
          omega
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat, List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

private theorem smtx_model_eval_str_prefixof_seq_eq
    (sx sy : SmtSeq) (T : SmtType)
    (hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T) :
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      SmtValue.Boolean
        (native_seq_prefix_eq (native_unpack_seq sx) (native_unpack_seq sy)) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hsxPack :
      native_pack_seq T xs = sx := by
    simpa [xs, hsxElem] using native_pack_unpack_seq sx
  have hExtract :
      native_seq_extract ys 0 (Int.ofNat xs.length) =
        ys.take xs.length := by
    exact native_seq_extract_zero_nat_any ys xs.length
  by_cases hPref :
      native_seq_prefix_eq xs ys = true
  · rcases (RuleProofs.native_seq_prefix_eq_iff xs ys).1 hPref with
      ⟨rest, hYs⟩
    have hTake : ys.take xs.length = xs := by
      rw [hYs]
      simp
    have hSeqEqExtract :
        sx =
          native_pack_seq T
            (native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length)) := by
      have hExtract' :
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
            native_unpack_seq sx := by
        calc
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
              ys.take xs.length := by
                simpa [xs, ys] using hExtract
          _ = xs := hTake
          _ = native_unpack_seq sx := rfl
      rw [hExtract']
      exact hsxPack.symm
    simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq, native_veq,
      native_seq_len, xs, ys, hsyElem, hPref]
    exact hSeqEqExtract
  · have hPrefFalse :
        native_seq_prefix_eq xs ys = false := by
      cases h : native_seq_prefix_eq xs ys
      · rfl
      · exact False.elim (hPref h)
    have hSeqNe :
        sx ≠ native_pack_seq T (ys.take xs.length) := by
      intro hEq
      have hList :
          xs = ys.take xs.length := by
        have hPackEq :
            native_pack_seq T xs =
              native_pack_seq T (ys.take xs.length) := by
          simpa [hsxPack] using hEq
        exact native_pack_seq_inj T hPackEq
      have hPrefTrue : native_seq_prefix_eq xs ys = true :=
        native_seq_prefix_eq_take_eq_true xs ys hList.symm
      rw [hPrefFalse] at hPrefTrue
      cases hPrefTrue
    have hSeqNeExtract :
        sx ≠
          native_pack_seq T
            (native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length)) := by
      have hExtract' :
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
            List.take (native_unpack_seq sx).length (native_unpack_seq sy) := by
        simpa [xs, ys] using hExtract
      intro hEq
      apply hSeqNe
      rwa [hExtract'] at hEq
    simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq, native_veq,
      native_seq_len, xs, ys, hsyElem, hPrefFalse]
    exact hSeqNeExtract

private theorem native_seq_extract_suffix_nat_suffix_local
    (xs : List SmtValue) (n : Nat) :
    ∃ pre,
      xs =
        pre ++
          native_seq_extract xs
            (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) := by
  by_cases hle : n <= xs.length
  · refine ⟨xs.take (xs.length - n), ?_⟩
    have hStart :
        Int.ofNat xs.length + -Int.ofNat n =
          Int.ofNat (xs.length - n) := by
      rw [← Int.sub_eq_add_neg]
      exact (Int.ofNat_sub hle).symm
    have hRem : xs.length - (xs.length - n) = n := by
      omega
    have hSub :=
      native_seq_extract_to_end_nat xs (xs.length - n)
        (Nat.sub_le xs.length n)
    rw [hRem] at hSub
    rw [hStart, hSub]
    exact (List.take_append_drop (xs.length - n) xs).symm
  · refine ⟨xs, ?_⟩
    have hlt : xs.length < n := Nat.lt_of_not_ge hle
    have hStartNeg :
        Int.ofNat xs.length + -Int.ofNat n < 0 := by
      have hltInt : (Int.ofNat xs.length : Int) < Int.ofNat n :=
        Int.ofNat_lt.mpr hlt
      omega
    have hExtract :
        native_seq_extract xs
          (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) = [] := by
      unfold native_seq_extract
      have hGuard :
          (decide (Int.ofNat xs.length + -Int.ofNat n < 0) ||
                decide (Int.ofNat n <= 0) ||
              decide
                (Int.ofNat xs.length + -Int.ofNat n >=
                  Int.ofNat xs.length)) =
            true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (Or.inl hStartNeg)
      rw [if_pos hGuard]
    rw [hExtract]
    simp

private theorem native_seq_extract_suffix_eq_of_append
    (pre xs : List SmtValue) :
    native_seq_extract (pre ++ xs)
        (Int.ofNat (pre ++ xs).length + -Int.ofNat xs.length)
        (Int.ofNat xs.length) =
      xs := by
  have hStart :
      Int.ofNat (pre ++ xs).length + -Int.ofNat xs.length =
        Int.ofNat pre.length := by
    simp
    omega
  have hSub :=
    native_seq_extract_to_end_nat (pre ++ xs) pre.length
      (by simp)
  have hRem : (pre ++ xs).length - pre.length = xs.length := by
    simp
  rw [hRem] at hSub
  rw [hStart, hSub]
  simp

private theorem native_seq_extract_suffix_eq_of_rev_prefix_true
    (xs ys : List SmtValue)
    (hPref :
      native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true) :
    native_seq_extract ys
        (Int.ofNat ys.length + -Int.ofNat xs.length)
        (Int.ofNat xs.length) =
      xs := by
  rcases (RuleProofs.native_seq_prefix_eq_iff
      (native_seq_rev xs) (native_seq_rev ys)).1 hPref with
    ⟨rest, hRev⟩
  have hRevList : ys.reverse = xs.reverse ++ rest := by
    simpa [native_seq_rev] using hRev
  have hYs : ys = rest.reverse ++ xs := by
    have h := congrArg List.reverse hRevList
    simpa [List.reverse_append] using h
  rw [hYs]
  exact native_seq_extract_suffix_eq_of_append rest.reverse xs

private theorem native_seq_rev_prefix_true_of_suffix_extract_eq
    (xs ys : List SmtValue)
    (hExtract :
      xs =
        native_seq_extract ys
          (Int.ofNat ys.length + -Int.ofNat xs.length)
          (Int.ofNat xs.length)) :
    native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true := by
  rcases native_seq_extract_suffix_nat_suffix_local ys xs.length with
    ⟨pre, hYs⟩
  rw [← hExtract] at hYs
  rw [RuleProofs.native_seq_prefix_eq_iff]
  refine ⟨pre.reverse, ?_⟩
  rw [hYs]
  simp [native_seq_rev, List.reverse_append]

private theorem smtx_model_eval_str_suffixof_seq_eq
    (sx sy : SmtSeq) (T : SmtType)
    (hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T) :
    __smtx_model_eval_str_suffixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      SmtValue.Boolean
        (native_seq_prefix_eq (native_seq_rev (native_unpack_seq sx))
          (native_seq_rev (native_unpack_seq sy))) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hsxPack :
      native_pack_seq T xs = sx := by
    simpa [xs, hsxElem] using native_pack_unpack_seq sx
  by_cases hPref :
      native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true
  · have hExtract :
        native_seq_extract ys
            (Int.ofNat ys.length + -Int.ofNat xs.length)
            (Int.ofNat xs.length) =
          xs :=
      native_seq_extract_suffix_eq_of_rev_prefix_true xs ys hPref
    have hSeqEq :
        sx =
          native_pack_seq T
            (native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length)) := by
      rw [hExtract]
      exact hsxPack.symm
    simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq,
      __smtx_model_eval__, native_veq, native_seq_len, xs, ys, hsyElem,
      hPref]
    exact hSeqEq
  · have hPrefFalse :
        native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) =
          false := by
      cases h : native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys)
      · rfl
      · exact False.elim (hPref h)
    have hSeqNe :
        sx ≠
          native_pack_seq T
            (native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length)) := by
      intro hEq
      have hList :
          xs =
            native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length) := by
        have hPackEq :
            native_pack_seq T xs =
              native_pack_seq T
                (native_seq_extract ys
                  (Int.ofNat ys.length + -Int.ofNat xs.length)
                  (Int.ofNat xs.length)) := by
          simpa [hsxPack] using hEq
        exact native_pack_seq_inj T hPackEq
      have hPrefTrue :
          native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) =
            true :=
        native_seq_rev_prefix_true_of_suffix_extract_eq xs ys hList
      rw [hPrefFalse] at hPrefTrue
      cases hPrefTrue
    simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq,
      __smtx_model_eval__, native_veq, native_seq_len, xs, ys, hsyElem,
      hPrefFalse]
    exact hSeqNe

private theorem str_value_len_eval_seq_length
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ x T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ->
      __str_value_len x ≠ Term.Stuck ->
      ∃ sx n,
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
          __str_value_len x = Term.Numeral n ∧
          n = Int.ofNat (native_unpack_seq sx).length := by
  intro x
  induction x using __str_value_len.induct with
  | case1 =>
      intro T hxTy _hLenNe
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hxTy
      rw [TranslationProofs.smtx_typeof_none] at hxTy
      cases hxTy
  | case2 e ss ih =>
      intro T hxTy hLenNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      have hTailNe : __str_value_len ss ≠ Term.Stuck := by
        intro hTail
        change __eo_add (Term.Numeral 1) (__str_value_len ss) ≠
          Term.Stuck at hLenNe
        rw [hTail] at hLenNe
        simp [__eo_add] at hLenNe
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ss T (by simpa [head] using hxTy)
      obtain ⟨stail, ntail, hTailEval, hTailLen, hNtail⟩ :=
        ih T hTailTy hTailNe
      obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
      obtain ⟨sxy, hWholeEval, hWholeUnp⟩ :=
        RuleProofs.concat_unpack M head ss shead stail hHeadEval hTailEval
      refine ⟨sxy, native_zplus (1 : native_Int) ntail,
        by simpa [head] using hWholeEval, ?_, ?_⟩
      · change __eo_add (Term.Numeral 1) (__str_value_len ss) =
          Term.Numeral (native_zplus (1 : native_Int) ntail)
        rw [hTailLen]
        simp [__eo_add]
      · rw [hWholeUnp, hHeadUnp, hNtail]
        simp [native_zplus]
        exact Int.add_comm 1 (Int.ofNat (native_unpack_seq stail).length)
  | case3 U =>
      intro T hxTy _hLenNe
      change __smtx_typeof
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtType.Seq T at hxTy
      refine ⟨SmtSeq.empty T, 0, ?_, by simp [__str_value_len], ?_⟩
      · change __smtx_model_eval M
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
          SmtValue.Seq (SmtSeq.empty T)
        cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) with
        | Seq A =>
            simp [__eo_to_smt_seq_empty, hTy] at hxTy ⊢
            rw [smtx_typeof_seq_empty_term_eq] at hxTy
            have hGuardNN :
                __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
                  SmtType.None := by
              rw [hxTy]
              exact seq_ne_none T
            have hGuard :
                __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) =
                  SmtType.Seq A :=
              smtx_typeof_guard_wf_of_non_none (SmtType.Seq A)
                (SmtType.Seq A) hGuardNN
            rw [hGuard] at hxTy
            injection hxTy with hA
            subst A
            rw [smtx_eval_seq_empty_term_eq]
        | _ =>
            simp [__eo_to_smt_seq_empty, hTy,
              TranslationProofs.smtx_typeof_none] at hxTy
      · simp [native_unpack_seq]
  | case4 e =>
      intro T hxTy _hLenNe
      obtain ⟨sa, hEval, hUnp⟩ := RuleProofs.eval_seqUnitAtom M e
      refine ⟨sa, 1, hEval, by simp [__str_value_len], ?_⟩
      rw [hUnp]
      simp
  | case5 s hs1 hs2 hs3 =>
      intro T hxTy hLenNe
      cases s <;>
        simp [__str_value_len, __eo_requires, __eo_is_str,
          __eo_is_str_internal, __eo_len, native_ite, native_teq,
          SmtEval.native_and, SmtEval.native_not] at hLenNe ⊢
      case String a h4 =>
        refine ⟨native_pack_string a, ?_, ?_⟩
        · change __smtx_model_eval M (SmtTerm.String a) =
            SmtValue.Seq (native_pack_string a)
          rw [__smtx_model_eval.eq_4]
        · rw [RuleProofs.unpack_pack_string_map]
          simp [native_str_len]

private theorem str_rev_guard_is_z (t : Term)
    (h : __eo_ite (__eo_is_str t) (Term.Boolean false)
      (__eo_is_z (__str_value_len t)) = Term.Boolean true) :
    __eo_is_z (__str_value_len t) = Term.Boolean true := by
  cases t <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      native_ite, native_teq, SmtEval.native_and, SmtEval.native_not] at h ⊢
  all_goals exact h

private theorem smt_typeof_str_rev_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)) =
      SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) = SmtType.Seq T
  rw [typeof_str_rev_eq, hxTy]
  simp [__smtx_typeof_seq_op_1]

private theorem smt_value_rel_str_rev_seq_unit_snoc
    (M : SmtModel) (hM : model_total_typed M)
    (e tail : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail)
          (Term.Apply (Term.UOp UserOp.seq_unit) e))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hTailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tail)
    (SmtType.Seq T) hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨stail, hTailEval⟩
  obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
  have hTailSeqTy : __smtx_typeof_seq_value stail = SmtType.Seq T := by
    simpa [hTailEval, __smtx_typeof_value] using hTailValTy
  have hTailElem : __smtx_elem_typeof_seq_value stail = T :=
    elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
  have hHeadValTy := smt_model_eval_preserves_type M hM (__eo_to_smt head)
    (SmtType.Seq T) (by simpa [head] using hHeadTy) (seq_ne_none T)
    (type_inhabited_seq T)
  have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
    simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
  have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
    elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq]
  change __smtx_model_eval_eq
    (__smtx_model_eval_str_concat
      (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt tail)))
      (__smtx_model_eval M (__eo_to_smt head)))
    (__smtx_model_eval M
      (SmtTerm.str_rev (__eo_to_smt (mkConcat head tail)))) =
      SmtValue.Boolean true
  rw [__smtx_model_eval.eq_88, __smtx_model_eval.eq_88]
  rw [smtx_model_eval_str_concat_term_eq, hTailEval, hHeadEval]
  simp [__smtx_model_eval_str_rev, __smtx_model_eval_str_concat,
    native_seq_rev, native_seq_concat, hTailElem, hHeadElem, hHeadUnp,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, List.reverse_cons,
    __smtx_model_eval_eq, native_veq]

private theorem smt_value_rel_str_rev_list_nil_empty
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev (__smtx_model_eval M (__eo_to_smt nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  cases hEval : __smtx_model_eval M (__eo_to_smt nil) with
  | Seq s =>
      rw [hEval] at hNilRel
      cases s with
      | empty U =>
          simp [__smtx_model_eval_str_rev, __smtx_model_eval_eq,
            native_veq] at hNilRel ⊢
          subst T
          rfl
      | cons v vs =>
          simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | _ =>
      rw [hEval] at hNilRel
      simp [__smtx_model_eval_eq, native_veq] at hNilRel

private theorem smt_value_rel_str_rev_list_nil_empty_term
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt nil)))
    (SmtValue.Seq (SmtSeq.empty T))
  rw [__smtx_model_eval.eq_88]
  exact smt_value_rel_str_rev_list_nil_empty M nil T hNil hNilTy

private theorem smt_value_rel_seq_nil_to_str_rev
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt nil))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil))) := by
  have hNilEmpty := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  have hRevEmpty :=
    smt_value_rel_str_rev_list_nil_empty_term M nil T hNil hNilTy
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt nil))
    (SmtValue.Seq (SmtSeq.empty T))
    (__smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
    hNilEmpty
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
      (SmtValue.Seq (SmtSeq.empty T)) hRevEmpty)

private theorem smt_value_rel_seq_unit_to_str_rev
    (M : SmtModel) (hM : model_total_typed M) (e : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
  have hHeadValTy := smt_model_eval_preserves_type M hM (__eo_to_smt head)
    (SmtType.Seq T) (by simpa [head] using hHeadTy) (seq_ne_none T)
    (type_inhabited_seq T)
  have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
    simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
  have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
    elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
  unfold RuleProofs.smt_value_rel
  change __smtx_model_eval_eq
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt head))) =
      SmtValue.Boolean true
  rw [__smtx_model_eval.eq_88, hHeadEval]
  simp only [__smtx_model_eval_str_rev, native_seq_rev, hHeadElem]
  rw [hHeadUnp]
  simp [List.reverse_cons, List.reverse_nil]
  rw [← hHeadUnp]
  change RuleProofs.smt_seq_rel shead
    (native_pack_seq T (native_unpack_seq shead))
  exact smt_seq_rel_pack_unpack T shead hHeadElem

private theorem smt_value_rel_elim_rev_seq_unit_cons_nil
    (M : SmtModel) (hM : model_total_typed M)
    (e nil : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil) ≠
          Term.Stuck)
    (hElimCons :
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)) ≠
            Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T (by simpa [head] using hHeadTy)
      hNilTy
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil
      (by simpa [head] using hRevCons)
  have hElimCons' : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevConsEq, head] using hElimCons
  have hLhsToCons : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T hConsTy
      hElimCons'
  have hConsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T
      (by simpa [head] using hHeadTy) hNil hNilTy
  have hRevNilTy :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev) nil)) = SmtType.Seq T :=
    smt_typeof_str_rev_of_seq nil T hNilTy
  have hRevNilEmpty :=
    smt_value_rel_str_rev_list_nil_empty_term M nil T hNil hNilTy
  have hConcatRevNilHeadToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_left_of_rel_empty M hM
      (Term.Apply (Term.UOp UserOp.str_rev) nil) head T
      hRevNilTy (by simpa [head] using hHeadTy) hRevNilEmpty
  have hSnoc :=
    smt_value_rel_str_rev_seq_unit_snoc M hM e nil T
      (by simpa [head] using hHeadTy) hNilTy
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_model_eval M (__eo_to_smt
      (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head nil))))
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead)
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head nil))))
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
        (__smtx_model_eval M (__eo_to_smt head)) hConcatRevNilHeadToHead)
      (by simpa [head] using hSnoc))

private theorem smt_value_rel_elim_rev_seq_unit_list
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ ss e T,
      __eo_is_list (Term.UOp UserOp.str_concat)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss) =
          Term.Boolean true ->
      __smtx_typeof (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)) =
          SmtType.Seq T ->
      (∃ n, __str_value_len
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss) =
          Term.Numeral n) ->
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)) ≠
            Term.Stuck ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)))))
          (__smtx_model_eval M (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_rev)
              (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)))) := by
  intro ss
  induction ss using __str_value_len.induct with
  | case1 =>
      intro e T hList _hTy _hLen
      simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
        native_ite, native_teq, SmtEval.native_not] at hList
  | case2 e2 ss2 ih =>
      intro e T hList hConsTy hLenEx
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let tailHead := Term.Apply (Term.UOp UserOp.seq_unit) e2
      let tail := mkConcat tailHead ss2
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true := by
        simpa [head, tail, tailHead] using
          eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
            head tail hList
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head tail T
          (by simpa [head, tail, tailHead] using hConsTy)
      rcases hLenEx with ⟨n, hLen⟩
      have hTailLenEx : ∃ m, __str_value_len tail = Term.Numeral m := by
        simpa [tail, tailHead] using
          RuleProofs.value_len_tail_numeral_of_concat_seqUnit e tail n
            (by simpa [head, tail, tailHead] using hLen)
      have hRevCons :
          __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
            Term.Stuck :=
        eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
          (mkConcat head tail) (by simpa [head, tail, tailHead] using hList)
      have hElimCons :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)) ≠ Term.Stuck :=
        str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head tail T
          (by simpa [head, tail, tailHead] using hConsTy) hRevCons
      refine ⟨by simpa [head, tail, tailHead] using hElimCons, ?_⟩
      obtain ⟨hElimTail, hTailRel⟩ := ih e2 T hTailList hTailTy hTailLenEx
      have hRevTail :
          __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck :=
        eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
          tail hTailList
      have hConsToSnoc : RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)))))
          (__smtx_model_eval M (__eo_to_smt
            (mkConcat
              (__str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
              head))) := by
        have hInterp :=
          eo_interprets_rev_cons_snoc_of_seq M hM head tail T hHeadTy
            hTailList hTailTy hRevCons hRevTail hElimCons hElimTail
        exact RuleProofs.eo_interprets_eq_rel M
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
          (mkConcat
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
            head) hInterp
      have hElimTailTy :
          __smtx_typeof (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))) =
            SmtType.Seq T :=
        smt_typeof_str_nary_elim_list_rev_of_seq tail T hTailList hTailTy
          hRevTail hElimTail
      have hRevTailTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) tail)) =
            SmtType.Seq T :=
        smt_typeof_str_rev_of_seq tail T hTailTy
      have hSnocCong : RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt
            (mkConcat
              (__str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
              head)))
          (__smtx_model_eval M (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail) head))) :=
        strConcat_smt_value_rel_left_congr M hM
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          (Term.Apply (Term.UOp UserOp.str_rev) tail) head T
          hElimTailTy hRevTailTy hHeadTy hTailRel
      have hSnoc :=
        smt_value_rel_str_rev_seq_unit_snoc M hM e tail T hHeadTy hTailTy
      exact RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
            head)))
        (__smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head tail))))
        hConsToSnoc
        (RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt
            (mkConcat
              (__str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
              head)))
          (__smtx_model_eval M (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail) head)))
          (__smtx_model_eval M (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head tail))))
          hSnocCong hSnoc)
  | case3 U =>
      intro e T hList hConsTy _hLenEx
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let nil := Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true := by
        simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat]
      obtain ⟨hHeadTy, hNilTy⟩ :=
        strConcat_args_of_seq_type head nil T
          (by simpa [head, nil] using hConsTy)
      have hRevCons :
          __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
            Term.Stuck :=
        eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
          (mkConcat head nil) (by simpa [head, nil] using hList)
      have hElimCons :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head nil)) ≠ Term.Stuck :=
        str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head nil T
          (by simpa [head, nil] using hConsTy) hRevCons
      exact ⟨by simpa [head, nil] using hElimCons,
        by simpa [head, nil] using
          smt_value_rel_elim_rev_seq_unit_cons_nil M hM e nil T
            hHeadTy hNil hNilTy hRevCons hElimCons⟩
  | case4 e2 =>
      intro e T hList _hConsTy _hLenEx
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.UOp UserOp.seq_unit) e2) =
              Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)
          (Term.Apply (Term.UOp UserOp.seq_unit) e2) hList
      simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq,
        native_ite, SmtEval.native_ite, native_not, SmtEval.native_not]
        at hTailList
  | case5 s hsStuck hsConcat hsEmpty hsUnit =>
      intro e T hList hConsTy hLenEx
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) s =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          head s (by simpa [head] using hList)
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head s T (by simpa [head] using hConsTy)
      rcases hLenEx with ⟨n, hLen⟩
      have hTailLenEx : ∃ m, __str_value_len s = Term.Numeral m := by
        simpa [head] using
          RuleProofs.value_len_tail_numeral_of_concat_seqUnit e s n
            (by simpa [head] using hLen)
      rcases hTailLenEx with ⟨m, hTailLen⟩
      cases s <;>
        simp [__str_value_len, __eo_requires, __eo_is_str,
          __eo_is_str_internal, __eo_len, native_ite, native_teq,
          SmtEval.native_and, SmtEval.native_not] at hTailLen
      case String w =>
        cases w with
        | nil =>
            let nil := Term.String []
            have hNil :
                __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
                  Term.Boolean true := by
              simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq]
            have hRevCons :
                __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
                  Term.Stuck :=
              eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
                (mkConcat head nil) (by simpa [head, nil] using hList)
            have hElimCons :
                __str_nary_elim
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (mkConcat head nil)) ≠ Term.Stuck :=
              str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head nil T
                (by simpa [head, nil] using hConsTy) hRevCons
            exact ⟨by simpa [head, nil] using hElimCons,
              by simpa [head, nil] using
                smt_value_rel_elim_rev_seq_unit_cons_nil M hM e nil T
                  hHeadTy hNil (by simpa [nil] using hTailTy)
                  hRevCons hElimCons⟩
        | cons ch rest =>
            simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
              __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
              native_teq, native_ite, SmtEval.native_ite, native_not,
              SmtEval.native_not] at hTailList

private theorem seq_eval_smt_type_and_value_rel
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ t,
      __seq_eval t ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (__seq_eval t)) =
          __smtx_typeof (__eo_to_smt t) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
          (__smtx_model_eval M (__eo_to_smt t)) := by
  intro t hEvalNe hNN
  induction t using __seq_eval.induct with
  | case1 =>
      simp [__seq_eval] at hEvalNe
  | case2 t n =>
      let a := __str_nary_intro t
      let nth := __eo_list_nth (Term.UOp UserOp.str_concat) a n
      let guard :=
        __eo_ite (__eo_is_str t) (Term.Boolean false)
          (__eo_is_z (__str_value_len t))
      have hReqNe :
          __eo_requires guard (Term.Boolean true)
              (__seq_element_of_unit nth) ≠ Term.Stuck := by
        simpa [__seq_eval, a, nth, guard] using hEvalNe
      have hGuardTerm : guard = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guard (Term.Boolean true)
          (__seq_element_of_unit nth) hReqNe
      have hSeqEvalResult :
          __seq_eval (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) t) n) =
            __seq_element_of_unit nth := by
        simpa [__seq_eval, a, nth, guard] using
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true)
            (__seq_element_of_unit nth) hReqNe
      have hElemNe : __seq_element_of_unit nth ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          (__seq_element_of_unit nth) hReqNe
      rcases seq_element_of_unit_eq_of_ne_stuck nth hElemNe with
        ⟨e, hNthUnit, hElemEq⟩
      have hNthNe : nth ≠ Term.Stuck := by
        intro hStuck
        rw [hStuck] at hElemNe
        simp [__seq_element_of_unit] at hElemNe
      have hSeqNthNN :
          term_has_non_none_type
            (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)) := by
        unfold term_has_non_none_type
        simpa using hNN
      rcases seq_nth_args_of_non_none hSeqNthNN with
        ⟨T, htTy, hnTy⟩
      have hList :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true :=
        eo_list_nth_is_list_true_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hIntroNe : a ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) a hList
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
      have hNthRecEq :
          nth = __eo_list_nth_rec a n :=
        eo_list_nth_eq_rec_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hNthRecNe :
          __eo_list_nth_rec a n ≠ Term.Stuck :=
        eo_list_nth_rec_ne_stuck_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hNthRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_nth_rec a n)) =
            SmtType.Seq T :=
        smt_typeof_list_nth_rec_str_concat_of_seq a n T hList hATy
          hNthRecNe
      have hSeqUnitTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
            SmtType.Seq T := by
        rw [← hNthUnit, hNthRecEq]
        exact hNthRecTy
      have hETy : __smtx_typeof (__eo_to_smt e) = T :=
        (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e)
          (A := T) hSeqUnitTy).1
      have hGuardNN :
          __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        have hSeqNthTy :
            __smtx_typeof
                (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)) =
              __smtx_typeof_guard_wf T T := by
          rw [typeof_seq_nth_eq, htTy, hnTy]
          rfl
        unfold term_has_non_none_type at hSeqNthNN
        rw [hSeqNthTy] at hSeqNthNN
        exact hSeqNthNN
      have hGuard :
          __smtx_typeof_guard_wf T T = T :=
        smtx_typeof_guard_wf_of_non_none T T hGuardNN
      have hEvalEq :
          __seq_eval (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) t) n) =
            e := by
        rw [hSeqEvalResult]
        exact hElemEq
      constructor
      · rw [hEvalEq]
        change __smtx_typeof (__eo_to_smt e) =
          __smtx_typeof (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n))
        rw [hETy, typeof_seq_nth_eq, htTy, hnTy]
        change T = __smtx_typeof_guard_wf T T
        rw [hGuard]
      · rw [hEvalEq]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt e))
          (__smtx_model_eval M
            (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)))
        rw [smtx_model_eval_seq_nth_term]
        have hNthRecUnit :
            __eo_list_nth_rec a n =
              Term.Apply (Term.UOp UserOp.seq_unit) e := by
          rw [← hNthRecEq]
          exact hNthUnit
        have hFinish :
            __str_value_len a ≠ Term.Stuck ->
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt e))
                (__smtx_seq_nth M
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt n))) := by
          intro hLenA
          have hRelA :=
            smt_value_rel_seq_nth_list_rec_of_value_len M hM a n e T
              hList hATy hLenA hNthRecUnit hnTy
          have hIntroRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt t)) :=
            smt_value_rel_str_nary_intro M hM t T htTy
              (by simpa [a] using hIntroNe)
          have hCong :=
            smt_value_rel_seq_nth_left_congr M hM a t n T hATy htTy
              hnTy hIntroRel
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt e))
            (__smtx_seq_nth M
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt n)))
            (__smtx_seq_nth M
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval M (__eo_to_smt n))) hRelA hCong
        have hIsZ : __eo_is_z (__str_value_len t) = Term.Boolean true :=
          str_rev_guard_is_z t (by simpa [guard] using hGuardTerm)
        have hLenTNe : __str_value_len t ≠ Term.Stuck := by
          intro hStuck
          rw [hStuck] at hIsZ
          simp [__eo_is_z, __eo_is_z_internal, native_teq,
            SmtEval.native_and, SmtEval.native_not] at hIsZ
        rcases str_value_len_numeral_of_ne_stuck t hLenTNe with
          ⟨len, hLenT⟩
        rcases RuleProofs.value_len_numeral_cases t len hLenT with
            ⟨w, htString⟩ | ⟨head, tail, htCons⟩ |
            ⟨U, htEmpty⟩ | ⟨head, htUnit⟩
        · subst t
          simp [guard, __eo_is_str, __eo_is_str_internal, __eo_ite,
            native_ite, native_teq, SmtEval.native_and,
            SmtEval.native_not] at hGuardTerm
        · subst t
          exact hFinish (by simpa [a] using hLenTNe)
        · subst t
          have hStuck : __seq_element_of_unit nth = Term.Stuck := by
            simpa [a, nth] using
              seq_element_list_nth_intro_seq_empty_stuck U n
          exact False.elim (hElemNe hStuck)
        · subst t
          have hHeadTy :
              __smtx_typeof
                  (__eo_to_smt
                    (Term.Apply (Term.UOp UserOp.seq_unit) head)) =
                SmtType.Seq T := by
            simpa using htTy
          have hHeadArgTy :=
            (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt head)
              (A := T) hHeadTy).1
          have hHeadEoTyNe : __eo_typeof head ≠ Term.Stuck := by
            intro hHeadStuck
            have hHeadNN : __smtx_typeof (__eo_to_smt head) ≠ SmtType.None := by
              rw [hHeadArgTy]
              exact (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt head)
                (A := T) hHeadTy).2
            have hTypeMatch :=
              TranslationProofs.eo_to_smt_typeof_matches_translation head hHeadNN
            rw [hHeadStuck] at hTypeMatch
            have hNone :
                __smtx_typeof (__eo_to_smt head) = SmtType.None := by
              simpa [__eo_to_smt_type, TranslationProofs.smtx_typeof_none]
                using hTypeMatch
            exact hHeadNN hNone
          have hIntroEq :=
            RuleProofs.str_nary_intro_seqUnit_eq head hHeadEoTyNe
          have hTailLen :
              __str_value_len
                  (__seq_empty
                    (__eo_typeof
                      (Term.Apply (Term.UOp UserOp.seq_unit) head))) ≠
                Term.Stuck := by
            change __str_value_len
                (__seq_empty (__eo_typeof_seq_unit (__eo_typeof head))) ≠
              Term.Stuck
            cases hHeadTyEo : __eo_typeof head <;>
              simp [__eo_typeof_seq_unit, hHeadTyEo, __seq_empty,
                __str_value_len, __eo_requires, __eo_is_str,
                __eo_is_str_internal, __eo_len, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not] at hHeadEoTyNe ⊢
            case UOp op =>
              cases op <;>
                simp [__eo_typeof_seq_unit, hHeadTyEo, __seq_empty,
                  __str_value_len, __eo_requires, __eo_is_str,
                  __eo_is_str_internal, __eo_len, native_ite, native_teq,
                  SmtEval.native_and, SmtEval.native_not] at hHeadEoTyNe ⊢
          have hLenA : __str_value_len a ≠ Term.Stuck := by
            change
              __str_value_len
                (__str_nary_intro
                  (Term.Apply (Term.UOp UserOp.seq_unit) head)) ≠
                Term.Stuck
            rw [hIntroEq]
            change __eo_add (Term.Numeral 1)
                (__str_value_len
                  (__seq_empty
                    (__eo_typeof
                      (Term.Apply (Term.UOp UserOp.seq_unit) head)))) ≠
              Term.Stuck
            rcases str_value_len_numeral_of_ne_stuck
                (__seq_empty
                  (__eo_typeof
                    (Term.Apply (Term.UOp UserOp.seq_unit) head)))
                hTailLen with
              ⟨tailLen, hTailVal⟩
            rw [hTailVal]
            simp [__eo_add]
          exact hFinish hLenA
  | case3 t =>
      have hLenNe : __str_value_len (__str_nary_intro t) ≠ Term.Stuck := by
        simpa [__seq_eval] using hEvalNe
      rcases str_value_len_numeral_of_ne_stuck (__str_nary_intro t) hLenNe with
        ⟨n, hLen⟩
      have hLenTermNN :
          term_has_non_none_type (SmtTerm.str_len (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        simpa using hNN
      rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
          (typeof_str_len_eq (__eo_to_smt t)) hLenTermNN with
        ⟨T, htTy⟩
      constructor
      · change
          __smtx_typeof (__eo_to_smt (__str_value_len (__str_nary_intro t))) =
            __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        rw [hLen]
        change __smtx_typeof (SmtTerm.Numeral n) =
          __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        have hNumTy : __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int := by
          rw [__smtx_typeof.eq_2]
        rw [hNumTy]
        rw [typeof_str_len_eq]
        simp [__smtx_typeof_seq_op_1_ret, htTy]
      · have hIntroNe : __str_nary_intro t ≠ Term.Stuck :=
          str_value_len_arg_ne_stuck_of_ne_stuck (__str_nary_intro t) hLenNe
        have hTComponents :
            type_inhabited T ∧ __smtx_type_wf T = true := by
          have hSeqWF :
              __smtx_type_wf (SmtType.Seq T) = true := by
            have hGood :=
              smt_term_result_seq_components_wf_of_non_none
                (__eo_to_smt t)
                (by
                  unfold term_has_non_none_type
                  rw [htTy]
                  exact seq_ne_none T)
            simpa [htTy, type_result_seq_components_wf] using hGood
          exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
        have hIntroNN :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
              SmtType.None :=
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 hIntroNe
        have hIntroTy :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) =
              SmtType.Seq T :=
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            hIntroNN hIntroNe
        obtain ⟨sIntro, nIntro, hIntroEval, hIntroLen, hNIntro⟩ :=
          str_value_len_eval_seq_length M hM (__str_nary_intro t) T
            hIntroTy hLenNe
        have hLenIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (__str_value_len (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t)))) := by
          rw [hIntroLen]
          have hNumEval :
              __smtx_model_eval M (__eo_to_smt (Term.Numeral nIntro)) =
                SmtValue.Numeral nIntro := by
            change __smtx_model_eval M (SmtTerm.Numeral nIntro) =
              SmtValue.Numeral nIntro
            rw [__smtx_model_eval.eq_2]
          rw [hNumEval]
          change RuleProofs.smt_value_rel
            (SmtValue.Numeral nIntro)
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
          rw [smtx_eval_str_len_term_eq, hIntroEval]
          rw [hNIntro]
          simp [__smtx_model_eval_str_len, native_seq_len,
            RuleProofs.smt_value_rel_refl]
        have hIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy hIntroNe
        have hLenCongRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t))) := by
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
            (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)))
          rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq]
          exact smt_value_rel_model_eval_str_len_of_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
            (__smtx_model_eval M (__eo_to_smt t)) hIntroRel
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M
            (__eo_to_smt (__str_value_len (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp.str_len) (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t)))
          hLenIntroRel hLenCongRel
  | case4 t ts ih =>
      have hConcatNN :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)) ≠
            SmtType.None := hNN
      rcases str_concat_args_of_non_none t ts hConcatNN with
        ⟨T, htTy, htsTy⟩
      let a := __str_nary_intro t
      let z := __str_nary_intro (__seq_eval ts)
      let c := __eo_list_concat (Term.UOp UserOp.str_concat) a z
      have hCNe : c ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck c
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hLists :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true :=
        eo_list_concat_str_concat_lists_of_ne_stuck a z hCNe
      have hIntroTNe : a ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) a hLists.1
      have hIntroEvalTsNe : z ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) z hLists.2
      have hSeqEvalTsNe : __seq_eval ts ≠ Term.Stuck := by
        exact str_nary_intro_arg_ne_stuck_of_ne_stuck (__seq_eval ts)
          (by simpa [z] using hIntroEvalTsNe)
      have htsNN : __smtx_typeof (__eo_to_smt ts) ≠ SmtType.None := by
        rw [htsTy]
        exact seq_ne_none T
      rcases ih hSeqEvalTsNe htsNN with
        ⟨hSeqEvalTsTySame, hSeqEvalTsRel⟩
      have hSeqEvalTsTy :
          __smtx_typeof (__eo_to_smt (__seq_eval ts)) = SmtType.Seq T := by
        rw [hSeqEvalTsTySame, htsTy]
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
          (by
            simpa [a] using
              str_nary_intro_has_smt_translation_of_seq_wf t T htTy
                hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe))
          (by simpa [a] using hIntroTNe)
      have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck (__seq_eval ts) T
          hSeqEvalTsTy
          (by
            simpa [z] using
              str_nary_intro_has_smt_translation_of_seq_wf (__seq_eval ts) T
                hSeqEvalTsTy hTComponents.1 hTComponents.2
                (by simpa [z] using hIntroEvalTsNe))
          (by simpa [z] using hIntroEvalTsNe)
      have hCEqRec :
          c = __eo_list_concat_rec a z :=
        eo_list_concat_str_concat_eq_rec_of_ne_stuck a z hCNe
      have hRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
            SmtType.Seq T :=
        smt_typeof_list_concat_rec_str_concat_of_seq a z T hLists.1 hATy hZTy
      have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T := by
        rw [hCEqRec]
        exact hRecTy
      have hElimRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
            (__smtx_model_eval M (__eo_to_smt c)) :=
        smt_value_rel_str_nary_elim M hM c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hListRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) := by
        rw [hCEqRec]
        exact strConcat_smt_value_rel_list_concat_rec_eval M hM a z T
          hLists.1 hATy hZTy
      have hIntroTRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt t)) :=
        smt_value_rel_str_nary_intro M hM t T htTy
          (by simpa [a] using hIntroTNe)
      have hIntroEvalTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt (__seq_eval ts))) :=
        smt_value_rel_str_nary_intro M hM (__seq_eval ts) T
          hSeqEvalTsTy (by simpa [z] using hIntroEvalTsNe)
      have hZTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt ts)) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt z))
          (__smtx_model_eval M (__eo_to_smt (__seq_eval ts)))
          (__smtx_model_eval M (__eo_to_smt ts))
          hIntroEvalTsRel hSeqEvalTsRel
      have hConcatLeftRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z))) :=
        strConcat_smt_value_rel_left_congr M hM a t z T
          hATy htTy hZTy hIntroTRel
      have hConcatRightRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        strConcat_smt_value_rel_right_congr M hM t z ts T
          htTy hZTy htsTy hZTsRel
      have hConcatRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hListRel
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
            hConcatLeftRel hConcatRightRel)
      constructor
      · change __smtx_typeof (__eo_to_smt (__str_nary_elim c)) =
          __smtx_typeof (__eo_to_smt (mkConcat t ts))
        rw [smt_typeof_str_nary_elim_of_seq_ne_stuck c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)]
        exact (smt_typeof_str_concat_of_seq t ts T htTy htsTy).symm
      · change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hElimRel hConcatRel
  | case5 t n m =>
      sorry
  | case6 t s =>
      sorry
  | case7 t s r =>
      sorry
  | case8 t s r =>
      sorry
  | case9 t s n =>
      sorry
  | case10 t s =>
      let a := __str_nary_intro t
      let b := __str_nary_intro s
      have hPrefixNe : __seq_is_prefix a b ≠ Term.Stuck := by
        simpa [__seq_eval, a, b] using hEvalNe
      have hPrefixNN :
          term_has_non_none_type
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s)) := by
        unfold term_has_non_none_type
        simpa using hNN
      rcases seq_char_binop_args_of_non_none (op := SmtTerm.str_prefixof)
          (typeof_str_prefixof_eq (__eo_to_smt t) (__eo_to_smt s))
          hPrefixNN with
        ⟨htTy, hsTy⟩
      have hIntroTNe : a ≠ Term.Stuck :=
        seq_is_prefix_left_ne_stuck_of_ne_stuck a b hPrefixNe
      have hIntroSNe : b ≠ Term.Stuck :=
        seq_is_prefix_right_ne_stuck_of_ne_stuck a b hPrefixNe
      have hTComponents :
          type_inhabited SmtType.Char ∧
            __smtx_type_wf SmtType.Char = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq SmtType.Char) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none SmtType.Char)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf SmtType.Char hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t SmtType.Char htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s SmtType.Char hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t SmtType.Char htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq SmtType.Char := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s SmtType.Char hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      rcases seq_eval_of_seq_type M hM a SmtType.Char hATy with
        ⟨sx, hAEval⟩
      rcases seq_eval_of_seq_type M hM b SmtType.Char hBTy with
        ⟨sy, hBEval⟩
      have hPrefixEq :
          __seq_is_prefix a b =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        seq_prefix_eq_bool_native_char M hM a b sx sy
          hATy hBTy hAEval hBEval hPrefixNe
      constructor
      · change __smtx_typeof (__eo_to_smt (__seq_is_prefix a b)) =
          __smtx_typeof
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s))
        rw [hPrefixEq]
        change __smtx_typeof
            (SmtTerm.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))) =
          __smtx_typeof
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s))
        rw [__smtx_typeof.eq_1, typeof_str_prefixof_eq]
        simp [htTy, hsTy, native_Teq, native_ite]
      · have hSxTy :
            __smtx_typeof_seq_value sx = SmtType.Seq SmtType.Char :=
          smt_typeof_seq_value_of_eval_seq M hM a SmtType.Char sx
            hATy hAEval
        have hSyTy :
            __smtx_typeof_seq_value sy = SmtType.Seq SmtType.Char :=
          smt_typeof_seq_value_of_eval_seq M hM b SmtType.Char sy
            hBTy hBEval
        have hSeqPrefixEval :
            __smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) =
              SmtValue.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy)) := by
          rw [hAEval, hBEval]
          exact smtx_model_eval_str_prefixof_seq_eq sx sy SmtType.Char
            hSxTy hSyTy
        have hIntroTRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t SmtType.Char htTy
            (by simpa [a] using hIntroTNe)
        have hIntroSRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt s)) :=
          smt_value_rel_str_nary_intro M hM s SmtType.Char hsTy
            (by simpa [b] using hIntroSNe)
        have hPrefixRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)))
              (__smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s))) :=
          smt_value_rel_model_eval_str_prefixof_of_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s))
            hIntroTRel hIntroSRel
        have hEvalEq :
            __seq_eval
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) t) s) =
              __seq_is_prefix a b := by
          simp [__seq_eval, a, b]
        have hOrigEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) t) s)) =
              __smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s)) := by
          simpa using
            (show
              __smtx_model_eval M
                  (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s)) =
                __smtx_model_eval_str_prefixof
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt s)) by
              rw [__smtx_model_eval.eq_86])
        rw [hEvalEq]
        rw [hOrigEval]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_is_prefix a b)))
          (__smtx_model_eval_str_prefixof
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s)))
        rw [hPrefixEq]
        have hBoolEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Boolean
                    (native_seq_prefix_eq (native_unpack_seq sx)
                      (native_unpack_seq sy)))) =
              SmtValue.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy)) := by
          change __smtx_model_eval M
              (SmtTerm.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy))) =
            SmtValue.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))
          rw [__smtx_model_eval.eq_1]
        rw [hBoolEval]
        change RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (native_seq_prefix_eq (native_unpack_seq sx)
              (native_unpack_seq sy)))
          (__smtx_model_eval_str_prefixof
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s)))
        rw [← hSeqPrefixEval]
        exact hPrefixRel
  | case11 t s =>
      sorry
  | case12 t n =>
      sorry
  | case13 t =>
      let guard :=
        __eo_ite (__eo_is_str t) (Term.Boolean false)
          (__eo_is_z (__str_value_len t))
      let a := __str_nary_intro t
      let r := __eo_list_rev (Term.UOp UserOp.str_concat) a
      let out := __str_nary_elim r
      have hReqNe : __eo_requires guard (Term.Boolean true) out ≠
          Term.Stuck := by
        simpa [__seq_eval, guard, a, r, out] using hEvalNe
      have hGuard : guard = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guard (Term.Boolean true) out hReqNe
      have hSeqEq :
          __seq_eval (Term.Apply (Term.UOp UserOp.str_rev) t) = out := by
        simpa [__seq_eval, guard, a, r, out] using
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) out
            hReqNe
      have hOutNe : out ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          out hReqNe
      have hRevNe : r ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck r hOutNe
      have hList :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true :=
        eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
          a hRevNe
      have hIntroNe : a ≠ Term.Stuck :=
        eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
          a hRevNe
      have hRevNN :
          term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        simpa using hNN
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq (__eo_to_smt t)) hRevNN with
        ⟨T, htTy⟩
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
      have hIntroTy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
        simpa [r, out] using
          smt_typeof_str_nary_elim_list_rev_of_seq a T hList hIntroTy
            (by simpa [r] using hRevNe) (by simpa [r, out] using hOutNe)
      have hStrRevTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)) =
            SmtType.Seq T :=
        smt_typeof_str_rev_of_seq t T htTy
      constructor
      · rw [hSeqEq]
        change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t))
        rw [hOutTy, hStrRevTy]
      · rw [hSeqEq]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt out))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)))
        have hIsZ :
            __eo_is_z (__str_value_len t) = Term.Boolean true :=
          str_rev_guard_is_z t (by simpa [guard] using hGuard)
        have hLenNe : __str_value_len t ≠ Term.Stuck := by
          intro hStuck
          rw [hStuck] at hIsZ
          simp [__eo_is_z, __eo_is_z_internal, native_teq,
            native_and, native_not] at hIsZ
        rcases str_value_len_numeral_of_ne_stuck t hLenNe with ⟨n, hLen⟩
        rcases RuleProofs.value_len_numeral_cases t n hLen with
          ⟨w, ht⟩ | ⟨e, ss, ht⟩ | ⟨U, ht⟩ | ⟨e, ht⟩
        · subst t
          simp [guard, __eo_is_str, __eo_is_str_internal,
            native_ite, native_teq, SmtEval.native_and,
            SmtEval.native_not] at hGuard
        · subst t
          have hConsRel :=
            (smt_value_rel_elim_rev_seq_unit_list M hM ss e T
              (by simpa [a, __str_nary_intro] using hList)
              (by simpa using htTy)
              ⟨n, by simpa using hLen⟩).2
          simpa [a, r, out, __str_nary_intro] using hConsRel
        · subst t
          let nil :=
            Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
          have hNil :
              __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
                Term.Boolean true := by
            simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat]
          have hNotConcat : ¬ ∃ head tail : Term, nil = mkConcat head tail := by
            intro hConcat
            rcases hConcat with ⟨head, tail, hEq⟩
            change
              Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) =
                Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail
              at hEq
            cases hEq
          have hRevEq :
              __eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_nary_intro nil) =
                __str_nary_intro nil :=
            eo_list_rev_str_nary_intro_eq_of_not_str_concat nil hNotConcat
              (by simpa [nil, a] using hIntroNe)
              (by simpa [nil, a, r] using hRevNe)
          have hElimIntroNe :
              __str_nary_elim (__str_nary_intro nil) ≠ Term.Stuck := by
            simpa [nil, a, r, out, hRevEq] using hOutNe
          have hInterp :=
            eo_interprets_str_nary_elim_intro_eq_of_seq M hM nil T
              (by simpa [nil] using htTy)
              (by simpa [nil, a] using hIntroNN)
              (by simpa [nil, a] using hIntroNe)
              hElimIntroNe
          have hOutToNil : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt out))
              (__smtx_model_eval M (__eo_to_smt nil)) := by
            have hRel :=
              RuleProofs.eo_interprets_eq_rel M
                (__str_nary_elim (__str_nary_intro nil)) nil hInterp
            simpa [nil, a, r, out, hRevEq] using hRel
          have hNilToRev :=
            smt_value_rel_seq_nil_to_str_rev M nil T hNil
              (by simpa [nil] using htTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt out))
            (__smtx_model_eval M (__eo_to_smt nil))
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
            hOutToNil hNilToRev
        · subst t
          let head := Term.Apply (Term.UOp UserOp.seq_unit) e
          have hNotConcat : ¬ ∃ x y : Term, head = mkConcat x y := by
            intro hConcat
            rcases hConcat with ⟨x, y, hEq⟩
            change Term.Apply (Term.UOp UserOp.seq_unit) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y at hEq
            injection hEq with hFun _hArg
            cases hFun
          have hRevEq :
              __eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_nary_intro head) =
                __str_nary_intro head :=
            eo_list_rev_str_nary_intro_eq_of_not_str_concat head hNotConcat
              (by simpa [head, a] using hIntroNe)
              (by simpa [head, a, r] using hRevNe)
          have hElimIntroNe :
              __str_nary_elim (__str_nary_intro head) ≠ Term.Stuck := by
            simpa [head, a, r, out, hRevEq] using hOutNe
          have hInterp :=
            eo_interprets_str_nary_elim_intro_eq_of_seq M hM head T
              (by simpa [head] using htTy)
              (by simpa [head, a] using hIntroNN)
              (by simpa [head, a] using hIntroNe)
              hElimIntroNe
          have hOutToHead : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt out))
              (__smtx_model_eval M (__eo_to_smt head)) := by
            have hRel :=
              RuleProofs.eo_interprets_eq_rel M
                (__str_nary_elim (__str_nary_intro head)) head hInterp
            simpa [head, a, r, out, hRevEq] using hRel
          have hHeadToRev :=
            smt_value_rel_seq_unit_to_str_rev M hM e T
              (by simpa [head] using htTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt out))
            (__smtx_model_eval M (__eo_to_smt head))
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) head)))
            hOutToHead hHeadToRev
  | case14 t _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      constructor
      · simp [__seq_eval]
      · simpa [__seq_eval] using
          RuleProofs.smt_value_rel_refl
            (__smtx_model_eval M (__eo_to_smt t))

private theorem seq_eval_smt_value_rel
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hEvalNe : __seq_eval t ≠ Term.Stuck)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
      (__smtx_model_eval M (__eo_to_smt t)) :=
  (seq_eval_smt_type_and_value_rel M hM t hEvalNe hNN).2

theorem cmd_step_seq_eval_op_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_eval_op args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_eval_op args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_eval_op args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              change __eo_typeof (__eo_prog_seq_eval_op a1) = Term.Bool at hResultTy
              change __eo_prog_seq_eval_op a1 ≠ Term.Stuck at hProg
              cases a1 with
              | Apply f u =>
                  cases f with
                  | Apply eqop t =>
                      cases eqop with
                      | UOp op =>
                          cases op with
                          | eq =>
                              obtain ⟨hReqEq, hProgEq⟩ := seq_eval_op_shape hProg
                              have hArgTrans :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) := by
                                simpa [RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans.1
                              have hBodyTy :
                                  __eo_typeof
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
                                    Term.Bool := by
                                rw [← hProgEq]
                                exact hResultTy
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type _
                                  hArgTrans hBodyTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                  true
                                rw [hProgEq]
                                subst u
                                exact RuleProofs.eo_interprets_eq_of_rel M t
                                  (__seq_eval t) hEqBool <| by
                                    exact RuleProofs.smt_value_rel_symm
                                      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
                                      (__smtx_model_eval M (__eo_to_smt t))
                                      (seq_eval_smt_value_rel M hM t
                                        (by
                                          intro hStuck
                                          rw [hStuck] at hEqBool
                                          rcases
                                            RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                              t Term.Stuck hEqBool with
                                            ⟨hSame, hNN⟩
                                          have hStuckTy :
                                              __smtx_typeof (__eo_to_smt Term.Stuck) =
                                                SmtType.None := by
                                            change __smtx_typeof SmtTerm.None = SmtType.None
                                            exact TranslationProofs.smtx_typeof_none
                                          rw [hStuckTy] at hSame
                                          exact hNN hSame)
                                        ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                          t (__seq_eval t) hEqBool).2))
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hEqBool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
