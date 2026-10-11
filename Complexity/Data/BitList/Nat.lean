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

@[simp] theorem toNat_nil : toNat [] = 0 := rfl

@[simp] theorem toNat_cons (a : Bool) (xs : List Bool) :
    toNat (a :: xs) = a.toNat + 2 * toNat xs := rfl

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

/-- Subtract one from a canonical binary numeral, dropping its last bit when necessary. -/
@[simp] def decrement : List Bool → List Bool
  | [] => []
  | false :: xs => true :: decrement xs
  | true :: xs => if xs.isEmpty then [] else false :: xs

@[simp] theorem decrement_bits (n : ℕ) : decrement n.bits = (n - 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    cases b with
    | false =>
      have h : n ≠ 0 := by simpa using hn
      have he : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
      simp [Nat.bit, Nat.bit0_bits n h, ih, he]
    | true =>
      by_cases h : n = 0
      · subst n; simp [Nat.bit]
      · have hb : n.bits ≠ [] := by
          intro hb
          exact h (by simpa [hb, toNat] using (toNat_bits n).symm)
        simp [Nat.bit, Nat.bit0_bits n h, hb]

theorem length_decrement_le (xs : List Bool) : (decrement xs).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all; split <;> simp_all

/-- Add two little-endian bit strings with an incoming carry. -/
def addCarry (c : Bool) : List Bool → List Bool → List Bool
  | [], ys => if c then increment ys else ys
  | xs, [] => if c then increment xs else xs
  | a :: xs, b :: ys => (xor (xor a b) c) ::
      addCarry ((a && b) || (c && (a || b))) xs ys

theorem addCarry_bits (c : Bool) (m n : ℕ) :
    addCarry c m.bits n.bits = (m + n + c.toNat).bits := by
  induction m using Nat.binaryRec' generalizing c n with
  | zero => cases c <;> simp [addCarry]
  | bit a m hm ih =>
    induction n using Nat.binaryRec' with
    | zero =>
      cases c with
      | false => simp [addCarry, Nat.bits_append_bit _ _ hm]
      | true =>
        simpa [addCarry, Nat.bits_append_bit _ _ hm] using increment_bits (Nat.bit a m)
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hm, Nat.bits_append_bit _ _ hn, addCarry, ih]
      have he : Nat.bit a m + Nat.bit b n + c.toNat =
          Nat.bit (xor (xor a b) c) (m + n + ((a && b) || (c && (a || b))).toNat) := by
        cases a <;> cases b <;> cases c <;> simp [Nat.bit, Bool.toNat] <;> omega
      rw [he, Nat.bits_append_bit]
      intro h
      cases a <;> cases b <;> cases c <;> simp_all

/-- Compare from low to high; `c` is the comparison of the already consumed low digits. -/
def leAux (c : Bool) : List Bool → List Bool → Bool
  | [], [] => c
  | a :: xs, [] => leAux (!a && c) xs []
  | [], b :: ys => leAux (b || c) [] ys
  | a :: xs, b :: ys => leAux (if a == b then c else b) xs ys

theorem leAux_eq (c : Bool) (xs ys : List Bool) :
    leAux c xs ys = decide (toNat xs + (!c).toNat ≤ toNat ys) := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [leAux]
    | cons b ys ih =>
      rw [leAux, ih]
      cases b <;> cases c <;> simp
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [leAux, ih]
      cases a <;> cases c <;> simp
    | cons b ys =>
      rw [leAux, ih]
      cases a <;> cases b <;> cases c <;> simp
      all_goals omega

end Complexity.BitList
