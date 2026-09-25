/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Transition

/-!
# Configurations in deterministic execution traces

A recorded trace contains exactly the configurations at the bounded execution times,
including both time zero and the final time.
-/

@[expose] public section

namespace Complexity.Transition

variable {α : Type*}

/-- Membership in a deterministic trace is reachability at a time within its bound. -/
theorem mem_runTrace_id_iff (f : α → α) (n : ℕ) (a b : α) :
    b ∈ (runTrace (m := Id) (pure ∘ f) n a).run ↔
      ∃ i ≤ n, b = (runN (m := Id) (pure ∘ f) i a).run := by
  induction n generalizing a with
  | zero =>
    change b ∈ [a] ↔ ∃ i ≤ 0, b = (runN (m := Id) (pure ∘ f) i a).run
    simp only [List.mem_singleton, Nat.le_zero_eq, exists_eq_left]
    rfl
  | succ n ih =>
    change b ∈ a :: (runTrace (m := Id) (pure ∘ f) n (f a)).run ↔ _
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, hb⟩)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · exact ⟨i + 1, Nat.succ_le_succ hi, hb⟩
    · rintro ⟨i, hi, hb⟩
      cases i with
      | zero => exact Or.inl hb
      | succ i => exact Or.inr ⟨i, Nat.le_of_succ_le_succ hi, hb⟩

end Complexity.Transition
