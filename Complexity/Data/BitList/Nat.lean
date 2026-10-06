/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Nat.Digits.Lemmas

/-! # Little-endian binary arithmetic -/

@[expose] public section

namespace Complexity.BitList

/-- Interpret a little-endian bit string, allowing high zero padding. -/
def toNat (xs : List Bool) : ℕ := Nat.ofDigits 2 (xs.map Bool.toNat)

@[simp] theorem toNat_bits (n : ℕ) : toNat n.bits = n := by
  change Nat.ofDigits 2 (n.bits.map (fun b ↦ bif b then 1 else 0)) = n
  rw [← Nat.digits_two_eq_bits, Nat.ofDigits_digits]

/-- Increment a bit string by carrying across its low `true` bits. -/
@[simp] def increment : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: increment xs

@[simp] theorem increment_bits (n : ℕ) : increment n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    cases b with
    | false =>
      have h : n ≠ 0 := by simpa using hn
      simp [Nat.bit, Nat.bit0_bits n h]
    | true =>
      rw [show Nat.bit true n + 1 = 2 * (n + 1) by simp [Nat.bit]; omega]
      simp [Nat.bit, ih]

theorem length_increment_le (xs : List Bool) : (increment xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

end Complexity.BitList
