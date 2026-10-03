/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.IntMemory.Basic

/-! # Representing a work tape by its head symbol and two stacks -/

@[expose] public section

namespace Complexity.StackMachine.Tape

variable {Γ : Type*} [Inhabited Γ]

/-- The nearest cells are at the tops of the two stacks; omitted cells are blank. -/
structure Rep (m : IntMemory Γ) (p : ℤ) (left : List Γ) (head : Γ) (right : List Γ) : Prop where
  head_eq : m[p] = head
  left_eq (n : ℕ) : m[p - (n + 1 : ℕ)] = left[n]?.getD default
  right_eq (n : ℕ) : m[p + (n + 1 : ℕ)] = right[n]?.getD default

namespace Rep

variable {m : IntMemory Γ} {p : ℤ} {left right : List Γ} {head : Γ}

theorem empty (p : ℤ) : Rep (∅ : IntMemory Γ) p [] default [] := by
  constructor <;> simp

theorem write (h : Rep m p left head right) (w : Γ) :
    Rep (m.set p w) p left w right := by
  refine ⟨by simp, ?_, ?_⟩
  · intro n
    rw [IntMemory.getElem_set_of_ne _ _ (by omega)]
    exact h.left_eq n
  · intro n
    rw [IntMemory.getElem_set_of_ne _ _ (by omega)]
    exact h.right_eq n

theorem move_right (h : Rep m p left head right) (w : Γ) :
    Rep (m.set p w) (p + 1) (w :: left) (right.head?.getD default) right.tail := by
  have hw := h.write w
  constructor
  · simpa [List.head?_eq_getElem?] using hw.right_eq 0
  · intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [show p + 1 - (n + 1 + 1 : ℕ) = p - (n + 1 : ℕ) by omega]
      simpa using hw.left_eq n
  · intro n
    rw [show p + 1 + (n + 1 : ℕ) = p + (n + 1 + 1 : ℕ) by omega]
    simpa using hw.right_eq (n + 1)

theorem move_left (h : Rep m p left head right) (w : Γ) :
    Rep (m.set p w) (p - 1) left.tail (left.head?.getD default) (w :: right) := by
  have hw := h.write w
  constructor
  · simpa [List.head?_eq_getElem?] using hw.left_eq 0
  · intro n
    rw [show p - 1 - (n + 1 : ℕ) = p - (n + 1 + 1 : ℕ) by omega]
    simpa using hw.left_eq (n + 1)
  · intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [show p - 1 + (n + 1 + 1 : ℕ) = p + (n + 1 : ℕ) by omega]
      simpa using hw.right_eq n

end Rep
end Complexity.StackMachine.Tape
