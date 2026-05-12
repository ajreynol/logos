import Cpc.Proofs.Canonical.Basic
import Std

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

private theorem order_key_field_append_injective
    {xs ys restX restY : List Nat}
    (h :
      __smtx_order_key_field xs ++ restX =
        __smtx_order_key_field ys ++ restY) :
    xs = ys ∧ restX = restY := by
  simp [__smtx_order_key_field] at h
  rcases h with ⟨hlen, htail⟩
  have hxs : xs = ys := by
    have ht := congrArg (List.take xs.length) htail
    simpa [List.take_left, hlen] using ht
  subst ys
  have hrest := List.append_cancel_left htail
  exact ⟨rfl, hrest⟩

private theorem order_key_field_injective
    {xs ys : List Nat}
    (h : __smtx_order_key_field xs = __smtx_order_key_field ys) :
    xs = ys :=
  (order_key_field_append_injective
    (restX := []) (restY := []) (by simpa using h)).1

private theorem order_key_field2_injective
    {xs1 xs2 ys1 ys2 : List Nat}
    (h :
      __smtx_order_key_field xs1 ++ __smtx_order_key_field xs2 =
        __smtx_order_key_field ys1 ++ __smtx_order_key_field ys2) :
    xs1 = ys1 ∧ xs2 = ys2 := by
  have h1 := order_key_field_append_injective h
  rcases h1 with ⟨hxs1, hrest⟩
  exact ⟨hxs1, order_key_field_injective hrest⟩

private theorem order_key_field3_injective
    {xs1 xs2 xs3 ys1 ys2 ys3 : List Nat}
    (h :
      __smtx_order_key_field xs1 ++ __smtx_order_key_field xs2 ++
          __smtx_order_key_field xs3 =
        __smtx_order_key_field ys1 ++ __smtx_order_key_field ys2 ++
          __smtx_order_key_field ys3) :
    xs1 = ys1 ∧ xs2 = ys2 ∧ xs3 = ys3 := by
  have h1 := order_key_field_append_injective
    (xs := xs1) (ys := ys1)
    (restX := __smtx_order_key_field xs2 ++ __smtx_order_key_field xs3)
    (restY := __smtx_order_key_field ys2 ++ __smtx_order_key_field ys3)
    (by simpa [List.append_assoc] using h)
  rcases h1 with ⟨hxs1, hrest1⟩
  have h2 := order_key_field_append_injective
    (xs := xs2) (ys := ys2)
    (restX := __smtx_order_key_field xs3)
    (restY := __smtx_order_key_field ys3) hrest1
  rcases h2 with ⟨hxs2, hrest2⟩
  exact ⟨hxs1, hxs2, order_key_field_injective hrest2⟩

private theorem char_toNat_injective {c d : Char}
    (h : c.toNat = d.toNat) :
    c = d := by
  have hcd := congrArg Char.ofNat h
  simpa [Char.ofNat_toNat] using hcd

private theorem list_char_toNat_injective :
    ∀ {cs ds : List Char},
      cs.map Char.toNat = ds.map Char.toNat -> cs = ds
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | c :: cs, d :: ds, h => by
      simp at h
      rcases h with ⟨hcd, htail⟩
      have hcdEq : c = d := char_toNat_injective hcd
      have htailEq : cs = ds := @list_char_toNat_injective cs ds htail
      subst d
      subst ds
      rfl

private theorem order_key_string_injective
    {s t : String}
    (h : __smtx_order_key_string s = __smtx_order_key_string t) :
    s = t := by
  simp [__smtx_order_key_string] at h
  rcases h with ⟨_hlen, hchars⟩
  have hlist : s.toList = t.toList := list_char_toNat_injective hchars
  calc
    s = String.ofList s.toList := (String.ofList_toList).symm
    _ = String.ofList t.toList := by rw [hlist]
    _ = t := String.ofList_toList

private theorem order_key_int_injective
    {i j : Int}
    (h : __smtx_order_key_int i = __smtx_order_key_int j) :
    i = j := by
  cases i <;> cases j <;> simp [__smtx_order_key_int] at h
  · subst h
    rfl
  · subst h
    rfl

private theorem order_key_rat_injective
    {q r : Rat}
    (h : __smtx_order_key_rat q = __smtx_order_key_rat r) :
    q = r := by
  simp [__smtx_order_key_rat] at h
  rcases h with ⟨hnum, hden⟩
  exact Rat.ext (order_key_int_injective hnum) hden

mutual

private theorem reglan_order_key_injective
    {r s : SmtRegLan}
    (h : __smtx_reglan_order_key r = __smtx_reglan_order_key s) :
    r = s := by
  cases r <;> cases s <;> simp [__smtx_reglan_order_key] at h ⊢
  case char.char c d =>
    exact char_toNat_injective h
  case range.range lo hi lo' hi' =>
    exact ⟨char_toNat_injective h.1, char_toNat_injective h.2⟩
  case concat.concat r1 r2 s1 s2 =>
    rcases order_key_field2_injective h with ⟨h1, h2⟩
    exact ⟨reglan_order_key_injective h1, reglan_order_key_injective h2⟩
  case union.union r1 r2 s1 s2 =>
    rcases order_key_field2_injective h with ⟨h1, h2⟩
    exact ⟨reglan_order_key_injective h1, reglan_order_key_injective h2⟩
  case inter.inter r1 r2 s1 s2 =>
    rcases order_key_field2_injective h with ⟨h1, h2⟩
    exact ⟨reglan_order_key_injective h1, reglan_order_key_injective h2⟩
  case star.star r s =>
    exact reglan_order_key_injective (order_key_field_injective h)
  case comp.comp r s =>
    exact reglan_order_key_injective (order_key_field_injective h)

private theorem type_order_key_injective
    {T U : SmtType}
    (h : __smtx_type_order_key T = __smtx_type_order_key U) :
    T = U := by
  cases T <;> cases U <;> simp [__smtx_type_order_key] at h ⊢
  case BitVec.BitVec n m =>
    exact h
  case Map.Map T U T' U' =>
    rcases order_key_field2_injective h with ⟨hT, hU⟩
    exact ⟨type_order_key_injective hT, type_order_key_injective hU⟩
  case Set.Set T U =>
    exact type_order_key_injective (order_key_field_injective h)
  case Seq.Seq T U =>
    exact type_order_key_injective (order_key_field_injective h)
  case Datatype.Datatype s d t e =>
    rcases order_key_field2_injective h with ⟨hs, hd⟩
    exact ⟨order_key_string_injective hs, datatype_order_key_injective hd⟩
  case TypeRef.TypeRef s t =>
    exact order_key_string_injective (order_key_field_injective h)
  case USort.USort n m =>
    exact h
  case FunType.FunType T U T' U' =>
    rcases order_key_field2_injective h with ⟨hT, hU⟩
    exact ⟨type_order_key_injective hT, type_order_key_injective hU⟩
  case DtcAppType.DtcAppType T U T' U' =>
    rcases order_key_field2_injective h with ⟨hT, hU⟩
    exact ⟨type_order_key_injective hT, type_order_key_injective hU⟩

private theorem value_order_key_injective
    {v w : SmtValue}
    (h : __smtx_value_order_key v = __smtx_value_order_key w) :
    v = w := by
  cases v <;> cases w <;> simp [__smtx_value_order_key] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp at h ⊢
  case Numeral.Numeral i j =>
    exact order_key_int_injective (order_key_field_injective h)
  case Rational.Rational q r =>
    exact order_key_rat_injective (order_key_field_injective h)
  case Binary.Binary w n w' n' =>
    rcases order_key_field2_injective h with ⟨hw, hn⟩
    exact ⟨order_key_int_injective hw, order_key_int_injective hn⟩
  case Map.Map m n =>
    exact map_order_key_injective (order_key_field_injective h)
  case Fun.Fun m n =>
    exact map_order_key_injective (order_key_field_injective h)
  case Set.Set m n =>
    exact map_order_key_injective (order_key_field_injective h)
  case Seq.Seq s t =>
    exact seq_order_key_injective (order_key_field_injective h)
  case Char.Char c d =>
    exact char_toNat_injective h
  case UValue.UValue u n u' n' =>
    exact h
  case RegLan.RegLan r s =>
    exact reglan_order_key_injective (order_key_field_injective h)
  case DtCons.DtCons s d n t e m =>
    have h1 := order_key_field_append_injective h
    rcases h1 with ⟨hs, hrest⟩
    have h2 := order_key_field_append_injective hrest
    rcases h2 with ⟨hd, hn⟩
    simp at hn
    exact ⟨order_key_string_injective hs, datatype_order_key_injective hd, hn⟩
  case Apply.Apply f x g y =>
    rcases order_key_field2_injective h with ⟨hf, hx⟩
    exact ⟨value_order_key_injective hf, value_order_key_injective hx⟩

private theorem map_order_key_injective
    {m n : SmtMap}
    (h : __smtx_map_order_key m = __smtx_map_order_key n) :
    m = n := by
  cases m <;> cases n <;> simp [__smtx_map_order_key] at h ⊢
  case cons.cons i e m j f n =>
    have h' :
        __smtx_order_key_field (__smtx_value_order_key i) ++
            __smtx_order_key_field (__smtx_value_order_key e) ++
              __smtx_order_key_field (__smtx_map_order_key m) =
          __smtx_order_key_field (__smtx_value_order_key j) ++
            __smtx_order_key_field (__smtx_value_order_key f) ++
              __smtx_order_key_field (__smtx_map_order_key n) := by
      simpa [List.append_assoc] using h
    rcases order_key_field3_injective h' with ⟨hi, he, hm⟩
    exact ⟨value_order_key_injective hi, value_order_key_injective he,
      map_order_key_injective hm⟩
  case default.default T e U f =>
    rcases order_key_field2_injective h with ⟨hT, he⟩
    exact ⟨type_order_key_injective hT, value_order_key_injective he⟩

private theorem seq_order_key_injective
    {s t : SmtSeq}
    (h : __smtx_seq_order_key s = __smtx_seq_order_key t) :
    s = t := by
  cases s <;> cases t <;> simp [__smtx_seq_order_key] at h ⊢
  case cons.cons v s w t =>
    rcases order_key_field2_injective h with ⟨hv, hs⟩
    exact ⟨value_order_key_injective hv, seq_order_key_injective hs⟩
  case empty.empty T U =>
    exact type_order_key_injective (order_key_field_injective h)

private theorem datatype_order_key_injective
    {d e : SmtDatatype}
    (h : __smtx_datatype_order_key d = __smtx_datatype_order_key e) :
    d = e := by
  cases d <;> cases e <;> simp [__smtx_datatype_order_key] at h ⊢
  case sum.sum c d c' d' =>
    rcases order_key_field2_injective h with ⟨hc, hd⟩
    exact ⟨datatype_cons_order_key_injective hc,
      datatype_order_key_injective hd⟩

private theorem datatype_cons_order_key_injective
    {c d : SmtDatatypeCons}
    (h :
      __smtx_datatype_cons_order_key c =
        __smtx_datatype_cons_order_key d) :
    c = d := by
  cases c <;> cases d <;> simp [__smtx_datatype_cons_order_key] at h ⊢
  case cons.cons T c U d =>
    rcases order_key_field2_injective h with ⟨hT, hc⟩
    exact ⟨type_order_key_injective hT,
      datatype_cons_order_key_injective hc⟩

end

private theorem native_vcmp_compare_eq_lt
    {a b : SmtValue}
    (hCmp : native_vcmp a b = true) :
    compare (__smtx_value_order_key a) (__smtx_value_order_key b) =
      Ordering.lt := by
  unfold native_vcmp at hCmp
  cases h : compare (__smtx_value_order_key a) (__smtx_value_order_key b) <;>
    simp [h] at hCmp ⊢

private theorem native_vcmp_compare_ne_lt
    {a b : SmtValue}
    (hCmp : native_vcmp a b = false) :
    compare (__smtx_value_order_key a) (__smtx_value_order_key b) ≠
      Ordering.lt := by
  intro hLt
  simp [native_vcmp, hLt] at hCmp

private theorem compare_eq_gt_of_eq_lt
    {α : Type} [Ord α] [Std.OrientedOrd α]
    {a b : α}
    (h : compare a b = Ordering.lt) :
    compare b a = Ordering.gt := by
  have hSwap := Std.OrientedOrd.eq_swap (a := a) (b := b)
  rw [h] at hSwap
  cases hba : compare b a <;> simp [hba] at hSwap ⊢

private theorem compare_eq_lt_of_eq_gt
    {α : Type} [Ord α] [Std.OrientedOrd α]
    {a b : α}
    (h : compare a b = Ordering.gt) :
    compare b a = Ordering.lt := by
  have hSwap := Std.OrientedOrd.eq_swap (a := a) (b := b)
  rw [h] at hSwap
  cases hba : compare b a <;> simp [hba] at hSwap ⊢

private theorem compare_lt_trans
    {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    {a b c : α}
    (hab : compare a b = Ordering.lt)
    (hbc : compare b c = Ordering.lt) :
    compare a c = Ordering.lt := by
  have hLE :
      (compare a c).isLE = true :=
    Std.TransOrd.isLE_trans
      (by rw [hab]; rfl)
      (by rw [hbc]; rfl)
  cases hac : compare a c
  · rfl
  · have hacEq : a = c := Std.LawfulEqOrd.eq_of_compare hac
    subst c
    have hba : compare b a = Ordering.gt := compare_eq_gt_of_eq_lt hab
    rw [hba] at hbc
    cases hbc
  · rw [hac] at hLE
    cases hLE

/--
The strict order used by `native_vcmp` is the lexicographic order on a
transparent structural key for `SmtValue`. Its order laws reduce to the
standard `List Nat` order laws plus injectivity of the key encoder.
-/
theorem native_vcmp_flip
    {a b : SmtValue}
    (hNe : native_veq a b = false)
    (hCmp : native_vcmp a b = false) :
    native_vcmp b a = true := by
  let ka := __smtx_value_order_key a
  let kb := __smtx_value_order_key b
  have hNeValue : a ≠ b := ne_of_native_veq_false hNe
  have hNeKey : ka ≠ kb := by
    intro hKey
    exact hNeValue (value_order_key_injective hKey)
  have hNotLt : compare ka kb ≠ Ordering.lt := by
    simpa [ka, kb] using native_vcmp_compare_ne_lt hCmp
  cases hAB : compare ka kb
  · exact False.elim (hNotLt hAB)
  · have hKeyEq : ka = kb := Std.LawfulEqOrd.eq_of_compare hAB
    exact False.elim (hNeKey hKeyEq)
  · have hBA : compare kb ka = Ordering.lt := compare_eq_lt_of_eq_gt hAB
    simp [native_vcmp, ka, kb, hBA]

theorem native_vcmp_ne
    {a b : SmtValue}
    (hCmp : native_vcmp a b = true) :
    native_veq a b = false := by
  by_cases hEq : a = b
  · subst b
    simp [native_vcmp] at hCmp
  · simp [native_veq, hEq]

theorem native_vcmp_trans
    {a b c : SmtValue}
    (hab : native_vcmp a b = true)
    (hbc : native_vcmp b c = true) :
    native_vcmp a c = true := by
  have habLt := native_vcmp_compare_eq_lt hab
  have hbcLt := native_vcmp_compare_eq_lt hbc
  have hacLt :
      compare (__smtx_value_order_key a) (__smtx_value_order_key c) =
        Ordering.lt :=
    compare_lt_trans habLt hbcLt
  simp [native_vcmp, hacLt]

end Smtm
