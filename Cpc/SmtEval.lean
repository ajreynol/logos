module

public import Init

public section

set_option linter.unusedVariables false

namespace SmtEval

-- Not a block: SmtValue carries a Rational constructor whatever the input
-- signature is, and derives Ord, so this instance is always needed.
instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

-- A proof written against the published tree names its strings with this, so
-- it is kept for a signature that has no string of its own to build.

-- The part of the native layer that every generated file can see. What comes
-- out here is what more than one of them reaches, since a definition only one
-- reaches is emitted into that file instead. See
-- LeanMetaReduce::placeNativeDefs and plugins/lean_meta/lean_meta_native.lean.
abbrev native_Bool := Bool

abbrev native_Int := Int

abbrev native_Rat := Rat

abbrev native_Nat := Nat

abbrev native_Char := Nat

abbrev native_String := List native_Char

def native_char_valid (c : native_Char) : native_Bool :=
  c < 196608

def native_string_lit (s : String) : native_String :=
  s.toList.map Char.toNat

def native_ite {T : Type} (c : native_Bool) (t e : T) : T :=
  if c then t else e

def native_not : native_Bool -> native_Bool
  | x => Bool.not x

def native_and : native_Bool -> native_Bool -> native_Bool
  | x, y => x && y

def native_or : native_Bool -> native_Bool -> native_Bool
  | x, y => x || y

def native_zplus : native_Int -> native_Int -> native_Int
  | x, y => x+y

def native_zmult : native_Int -> native_Int -> native_Int
  | x, y => x*y

def native_zneg : native_Int -> native_Int
  | x => -x

def native_zeq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x = y)

def native_zleq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x <= y)

def native_zlt : native_Int -> native_Int -> native_Bool
  | x, y => decide (x < y)

def native_div_total : native_Int -> native_Int -> native_Int
  | x, y => x/y

def native_mod_total : native_Int -> native_Int -> native_Int
  | x, y => x%y

def native_zexp_total (x : native_Int) (y : native_Int) : native_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))

def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)

def native_piand : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt

def impl_native_pior : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ||| (BitVec.ofInt (Int.toNat w) y)).toInt

def impl_native_pixor : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ^^^ (BitVec.ofInt (Int.toNat w) y)).toInt

-- Rational arithmetic

def native_mk_rational : native_Int -> native_Int -> native_Rat
  | x, y => x/y

def native_qplus : native_Rat -> native_Rat -> native_Rat
  | x, y => x+y

def native_qmult : native_Rat -> native_Rat -> native_Rat
  | x, y => x*y

def native_qneg : native_Rat -> native_Rat
  | x => -x

def native_qlt : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x < y)

def native_qdiv_total : native_Rat -> native_Rat -> native_Rat
  | x, y => x/y

def native_to_int : native_Rat -> native_Int
  | x => (Rat.floor x)

def native_to_real : native_Int -> native_Rat
  | x => (native_mk_rational x 1)

-- Strings

def native_str_to_code (s : native_String) : native_Int :=
  match s with
  | [c] => if native_char_valid c then Int.ofNat c else -1
  | _   => -1

def native_str_from_code (i : native_Int) : native_String :=
  if (0 <= i && (native_char_valid (Int.toNat i))) then
    [(Int.toNat i)]
  else
    native_string_lit ""

def native_streq : native_String -> native_String -> native_Bool
  | x, y => decide (x = y)

def native_binary_and : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_piand w n1 n2))

def native_binary_or : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pior w n1 n2))

def native_binary_xor : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pixor w n1 n2))

def native_binary_not : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_int_pow2 w) (native_zneg (native_zplus n 1)))

def native_binary_max : native_Int -> native_Int
  | w => (native_zplus (native_int_pow2 w) (native_zneg 1))

def native_binary_concat : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  | w1, n1, w2, n2 => (native_zplus (native_zmult n1 (native_int_pow2 w2)) n2)

def native_binary_extract : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  -- The caller masks this quotient to width x1 - x2 + 1; w and x1 are carried
  -- here only to match the native EO operation's signature.
  | w, n, x1, x2 => (native_div_total n (native_int_pow2 x2))

-- Natural numbers

def native_int_to_nat (x : native_Int) : native_Nat :=
  (Int.toNat x)

syntax "native_nat_zero" : term
macro_rules
  | `(native_nat_zero) => `(Nat.zero)

syntax "native_nat_succ " term : term
macro_rules
  | `(native_nat_succ $x) => `(Nat.succ $x)

-- Strings of the checker. The Eunoia string operators are over Lean strings,
-- where the SMT-LIB ones are over sequences of values, so the two are
-- different functions of the layer rather than one shared by both.


end SmtEval
