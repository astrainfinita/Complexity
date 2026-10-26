/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Tree

/-! # Encodings of vectors

A vector uses the list encoding of its entries; its length is supplied by its type. -/

@[expose] public section

namespace Complexity

/-- Recover a vector from a list of the required length. -/
def List.decodeVector {α : Type*} (n : ℕ) (xs : List α) : Option (Vector α n) :=
  if h : xs.length = n then some ⟨xs.toArray, by simpa using h⟩ else none

theorem List.decodeVector_eq_some_iff {α : Type*} {n : ℕ} (xs : List α) (v : Vector α n) :
    List.decodeVector n xs = some v ↔ v.toList = xs := by
  unfold List.decodeVector
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      ext i hi
      simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact h (by simp)

/-- A vector uses the list of its entries. -/
instance {R α : Type*} [c : UniqueEncoding R (List α)] {n : ℕ} :
    UniqueEncoding R (Vector α n) :=
  c.ofLeftInjection Vector.toList (fun xs => Part.ofOption (List.decodeVector n xs))
    fun xs v => by
      simpa only [Part.mem_coe, Option.mem_def] using List.decodeVector_eq_some_iff xs v

theorem encode_vector {R α : Type*} [UniqueEncoding R (List α)] {n : ℕ} (v : Vector α n) :
    encode R v = encode R v.toList := rfl

@[dominated] theorem size_encode_vector_toList {α : Type*} [UniqueEncoding Tree α] {n : ℕ}
    (v : Vector α n) : ⌜v.toList⌝ₜ.size = ⌜v⌝ₜ.size :=
  rfl

end Complexity
