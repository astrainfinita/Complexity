/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Complexity.Encoding.Composition
public import Complexity.Data.BitList.Nat

/-! # Binary natural-number encodings

`Nat.bits` is the Boolean form of `Nat.digits 2`, least significant bit first.
Zero is the empty list; nonzero codes end in `true`. Tree codes use the existing list encoding.
-/

@[expose] public section

namespace Complexity.BitList

/-- Reject noncanonical high zero bits when decoding a natural number. -/
def decodeNat (xs : List Bool) : Option ℕ :=
  let n := toNat xs
  if n.bits = xs then some n else none

theorem decodeNat_eq_some_iff (xs : List Bool) (n : ℕ) :
    decodeNat xs = some n ↔ n.bits = xs := by
  by_cases h : n.bits = xs
  · subst xs; simp [decodeNat]
  · simp only [decodeNat]
    split <;> simp_all; aesop

end Complexity.BitList

namespace Complexity

/-- Canonical binary natural numbers, with no high zero padding. -/
instance : UniqueEncoding (List Bool) ℕ :=
  UniqueEncoding.ofOption Nat.bits BitList.decodeNat fun n xs ↦ BitList.decodeNat_eq_some_iff xs n

/-- Binary digits reuse the ordinary Boolean-list tree representation. -/
instance : UniqueEncoding Tree ℕ :=
  (inferInstance : UniqueEncoding Tree (List Bool)).comp inferInstance

@[simp] theorem encode_nat_bits (n : ℕ) : encode (List Bool) n = n.bits := rfl

@[simp] theorem encode_nat_tree (n : ℕ) : encode Tree n = encode Tree n.bits := rfl

/-- Binary increment grows the encoded tree by at most one digit. -/
theorem size_encode_increment_le (xs : List Bool) :
    (encode Tree (BitList.increment xs)).size ≤ (encode Tree xs).size + 4 := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all <;> omega

end Complexity
