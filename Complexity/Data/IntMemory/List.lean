/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.IntMemory

/-!
# Lists stored in integer memory

A list occupies the nonnegative addresses starting at zero. Appending one element writes at
the list's length, and erasing that address with `default` recovers the original memory.
-/

@[expose] public section

namespace Complexity.IntMemory

variable {α : Type*} [Inhabited α]

/-- Store a list starting at address zero; all other addresses contain `default`. -/
def ofList (xs : List α) : IntMemory α := ofArray xs.toArray

@[simp]
theorem ofList_nil : ofList ([] : List α) = ∅ := rfl

@[simp]
theorem nonneg_ofList (xs : List α) :
    (ofList xs).nonneg = NatMemory.ofArray xs.toArray := rfl

@[simp]
theorem neg_ofList (xs : List α) : (ofList xs).neg = ∅ := rfl

theorem getElem_ofList_natCast (xs : List α) (n : ℕ) :
    (ofList xs)[(n : ℤ)] = xs[n]?.getD default := by
  simp [ofList]

theorem getElem_ofList_negSucc (xs : List α) (n : ℕ) :
    (ofList xs)[Int.negSucc n] = default := by
  simp

theorem getElem_ofList_of_neg (xs : List α) {i : ℤ} (h : i < 0) :
    (ofList xs)[i] = default := by
  cases i with
  | ofNat n => simp only [Int.ofNat_eq_natCast] at h; omega
  | negSucc n => exact getElem_ofList_negSucc xs n

theorem getElem_ofList_of_lt (xs : List α) {n : ℕ} (h : n < xs.length) :
    (ofList xs)[(n : ℤ)] = xs[n] := by
  rw [getElem_ofList_natCast, List.getElem?_eq_getElem h, Option.getD_some]

theorem getElem_ofList_of_le (xs : List α) {n : ℕ} (h : xs.length ≤ n) :
    (ofList xs)[(n : ℤ)] = default := by
  rw [getElem_ofList_natCast, List.getElem?_eq_none h, Option.getD_none]

theorem getElem_ofList_length (xs : List α) :
    (ofList xs)[(xs.length : ℤ)] = default := getElem_ofList_of_le xs le_rfl

/-- Appending a suffix preserves all addresses in the prefix. -/
theorem getElem_ofList_append_left (xs ys : List α) {n : ℕ} (h : n < xs.length) :
    (ofList (xs ++ ys))[(n : ℤ)] = (ofList xs)[(n : ℤ)] := by
  rw [getElem_ofList_natCast, getElem_ofList_natCast, List.getElem?_append_left h]

theorem getElem_ofList_append_length (xs : List α) (a : α) :
    (ofList (xs ++ [a]))[(xs.length : ℤ)] = a := by
  rw [getElem_ofList_natCast, List.getElem?_append_right le_rfl]
  simp

/-- Appending one element is exactly one write at the first address past the list. -/
theorem set_ofList_length (xs : List α) (a : α) :
    (ofList xs).set xs.length a = ofList (xs ++ [a]) := by
  ext i
  cases i with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    by_cases h : n = xs.length
    · subst n
      rw [getElem_set_self, getElem_ofList_append_length]
    · rw [getElem_set_of_ne _ _ (by omega)]
      by_cases hn : n < xs.length
      · exact (getElem_ofList_append_left xs [a] hn).symm
      · rw [getElem_ofList_of_le xs (by omega), getElem_ofList_of_le _ (by simp; omega)]
  | negSucc n =>
    rw [getElem_set_of_ne _ _ (by omega)]
    rw [getElem_ofList_negSucc, getElem_ofList_negSucc]

/-- Erasing the last address of an appended list recovers the original memory. -/
theorem set_ofList_append_length (xs : List α) (a : α) :
    (ofList (xs ++ [a])).set xs.length default = ofList xs := by
  rw [← set_ofList_length, set_set, ← getElem_ofList_length xs, set_getElem]

@[simp]
theorem ofList_append_default (xs : List α) : ofList (xs ++ [default]) = ofList xs := by
  rw [← set_ofList_length, ← getElem_ofList_length xs, set_getElem]

end Complexity.IntMemory
