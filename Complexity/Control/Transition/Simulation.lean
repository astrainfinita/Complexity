/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Transition.Basic

/-!
# Simulation of a finite execution segment

The step condition is needed only before the segment's endpoint. In particular,
a halted subroutine can be simulated by a machine which continues afterwards.
-/

@[expose] public section

namespace Complexity.Transition

variable {α β : Type*} {f : α → α} {g : β → β}
  {R : α → β → Prop} {a : α} {b : β} {n : ℕ}

/-- Preserve a relation for exactly the steps of a given source execution. -/
theorem rel_runN_of_step (hab : R a b)
    (h : ∀ i < n, ∀ b, R ((runN (m := Id) (pure ∘ f) i a).run) b →
      R ((runN (m := Id) (pure ∘ f) (i + 1) a).run) (g b)) :
    R ((runN (m := Id) (pure ∘ f) n a).run) ((runN (m := Id) (pure ∘ g) n b).run) := by
  induction n with
  | zero => exact hab
  | succ n ih =>
      rw [runN_succ' (m := Id) (pure ∘ g)]
      exact h n (Nat.lt_succ_self n) _
        (ih fun i hi ↦ h i (Nat.lt_trans hi (Nat.lt_succ_self n)))

/-- Simulate an execution segment whose source has not halted before its endpoint. -/
theorem rel_runN_of_not_halted {H : α → Prop} (hab : R a b)
    (h : ∀ a b, R a b → ¬H a → R (f a) (g b))
    (hn : ∀ i < n, ¬H ((runN (m := Id) (pure ∘ f) i a).run)) :
    R ((runN (m := Id) (pure ∘ f) n a).run) ((runN (m := Id) (pure ∘ g) n b).run) := by
  apply rel_runN_of_step hab
  intro i hi b hab
  rw [runN_succ' (m := Id) (pure ∘ f)]
  exact h _ b hab (hn i hi)

/-- A relation preserved by each step is preserved by every finite run. -/
theorem rel_runN (h : ∀ a b, R a b → R (f a) (g b)) (hab : R a b) (n : ℕ) :
    R ((runN (m := Id) (pure ∘ f) n a).run) ((runN (m := Id) (pure ∘ g) n b).run) := by
  apply rel_runN_of_step hab
  intro i _ b hab
  rw [runN_succ' (m := Id) (pure ∘ f)]
  exact h _ b hab

/-- A map commuting with one transition commutes with an entire run. -/
theorem runN_map (encode : α → β) (h : ∀ a, g (encode a) = encode (f a))
    (a : α) (n : ℕ) :
    (runN (m := Id) (pure ∘ g) n (encode a)).run =
      encode ((runN (m := Id) (pure ∘ f) n a).run) :=
  rel_runN (R := fun a b ↦ b = encode a)
    (by rintro a _ rfl; exact h a) rfl n

end Complexity.Transition
