/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.IntMemory.List
public import Complexity.Data.FinEnum

/-! # Binary words surrounded by blank tape cells -/

@[expose] public section

namespace Complexity.TM.Program.Word

/-- Bits occupy addresses from zero; every other cell is blank. -/
def tape (xs : List Bool) : IntMemory (Option Bool) := IntMemory.ofList (xs.map some)

@[simp] theorem tape_empty : tape [] = ∅ := by simp [tape]

/-- Natural addresses read the corresponding optional list element. -/
theorem tape_get (xs : List Bool) (n : ℕ) : (tape xs)[(n : ℤ)] = xs[n]? := by
  simp [tape]
  cases xs[n]? <;> rfl

theorem tape_neg (xs : List Bool) (n : ℕ) :
    (tape xs)[Int.negSucc n] = none := by simp [tape]; rfl

@[simp] theorem tape_left (xs : List Bool) : (tape xs)[(-1 : ℤ)] = none := tape_neg xs 0

theorem tape_length (xs : List Bool) : (tape xs)[(xs.length : ℤ)] = none := by
  rw [tape_get]
  simp

theorem tape_append (xs : List Bool) (a : Bool) :
    (tape xs).set xs.length (some a) = tape (xs ++ [a]) := by
  simpa [tape] using IntMemory.set_ofList_length (xs.map some) (some a)

/-- Erasing the last bit restores the complete preceding word. -/
theorem tape_erase_append (xs : List Bool) (a : Bool) :
    (tape (xs ++ [a])).set xs.length none = tape xs := by
  simpa [tape, show (default : Option Bool) = none from rfl] using
    IntMemory.set_ofList_append_length (xs.map some) (some a)

end Complexity.TM.Program.Word
