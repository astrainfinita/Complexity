/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Data.IntMemory
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory

open Complexity

local instance : Inhabited ℕ := ⟨7⟩

-- Lookup and growth must use the specified default, including gaps between stored values.
#guard (NatMemory.ofArray #[3, 4])[100] = 7
#guard ((NatMemory.ofArray #[3, 4]).set 5 9)[0] = 3
#guard ((NatMemory.ofArray #[3, 4]).set 5 9)[4] = 7
#guard ((NatMemory.ofArray #[3, 4]).set 5 9)[5] = 9
#guard ((NatMemory.ofArray #[3, 4]).set 5 9)[6] = 7
#guard ((NatMemory.ofArray #[3, 4]).set 1 9)[1] = 9

-- Padding and writing the default are invisible in the quotient, even far beyond the array.
example : NatMemory.ofArray #[1, 2, 7, 7] = NatMemory.ofArray #[1, 2] :=
  NatMemory.ofArray_append_replicate #[1, 2] 2

example : (∅ : NatMemory ℕ).set 100 7 = ∅ := by
  ext i
  simp [NatMemory.getElem_set, default]

example (xs : Array ℕ) (n i : ℕ) (a : ℕ) :
    (NatMemory.ofArray (xs ++ Array.replicate n 7)).set i a =
      (NatMemory.ofArray xs).set i a := by
  exact congrArg (fun m : NatMemory ℕ ↦ m.set i a) (NatMemory.ofArray_append_replicate xs n)

-- Negative addresses follow `Int.negSucc`, with no duplicated or omitted origin.
#guard (IntMemory.mk (NatMemory.ofArray #[10, 11]) (NatMemory.ofArray #[20, 21]))[(0 : ℤ)] = 10
#guard (IntMemory.mk (NatMemory.ofArray #[10, 11]) (NatMemory.ofArray #[20, 21]))[-1] = 20
#guard (IntMemory.mk (NatMemory.ofArray #[10, 11]) (NatMemory.ofArray #[20, 21]))[-2] = 21
#guard ((IntMemory.ofArray #[3, 4]).set (-1) 9)[(0 : ℤ)] = 3
#guard ((IntMemory.ofArray #[3, 4]).set (-1) 9)[-1] = 9
#guard ((IntMemory.ofArray #[3, 4]).set (-5) 9)[-4] = 7
#guard ((IntMemory.ofArray #[3, 4]).set (-5) 9)[-5] = 9
#guard ((IntMemory.ofArray #[3, 4]).set (-5) 9)[-6] = 7
#guard (((∅ : IntMemory ℕ).set (-1) 9).set 0 8)[-1] = 9

example : (∅ : IntMemory ℕ).set (-100) 7 = ∅ := by
  ext i
  simp [IntMemory.getElem_set, default]

example (m : IntMemory ℕ) : (m.set (-1) 9).set 0 8 = (m.set 0 8).set (-1) 9 := by
  exact IntMemory.set_comm m 9 8 (by decide)

-- Extensionality is available with only an inhabited stored type.
example {α : Type*} [Inhabited α] {m n : NatMemory α} (h : ∀ i : ℕ, m[i] = n[i]) : m = n := by
  ext i
  exact h i

example {α : Type*} [Inhabited α] {m n : IntMemory α} (h : ∀ i : ℤ, m[i] = n[i]) : m = n := by
  ext i
  exact h i
