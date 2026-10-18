/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree
public import Complexity.Encoding.Composition
public import Complexity.Data.BitList.Nat
public import Complexity.Tactic.TreeProgram.Attributes

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

/-- Binary digits reuse the ordinary Boolean-list tree representation. -/
instance : UniqueEncoding Tree ℕ :=
  (inferInstance : UniqueEncoding Tree (List Bool)).ofLeftInjection
    Nat.bits (fun xs ↦ Part.ofOption (BitList.decodeNat xs)) fun xs n ↦ by
      simpa only [Part.mem_coe, Option.mem_def] using BitList.decodeNat_eq_some_iff xs n

@[simp] theorem encode_nat_tree (n : ℕ) : ⌜n⌝ₜ = ⌜n.bits⌝ₜ := rfl

/-- Binary increment grows the encoded tree by at most one digit. -/
theorem size_encode_increment_le (xs : List Bool) :
    ⌜BitList.increment xs⌝ₜ.size ≤ ⌜xs⌝ₜ.size + 4 := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all <;> omega

/-- Incrementing a natural-number code adds at most one binary digit. -/
@[dominated] theorem size_encode_nat_succ_le (n : ℕ) : ⌜n + 1⌝ₜ.size ≤ ⌜n⌝ₜ.size + 4 := by
  simpa only [BitList.increment_bits, ← encode_nat_tree] using size_encode_increment_le n.bits

/-- A coarse numerical bound, useful when generating rather than merely reading indices. -/
theorem size_encode_nat_le (n : ℕ) : ⌜n⌝ₜ.size ≤ 4 * n + 1 := by
  induction n with
  | zero => simp
  | succ n ih => have := size_encode_nat_succ_le n; omega

@[dominated] theorem size_encode_range_le (n : ℕ) : ⌜List.range n⌝ₜ.size ≤ 3 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := size_encode_nat_le n
    have ha := size_encode_list_append (List.range n) [n]
    rw [List.range_succ]
    simp only [encode_list_cons, size_encode_prod, encode_list_nil, size_encode_unit] at ha
    nlinarith

end Complexity
