/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Transition
public import Mathlib.Data.Nat.Basic

/-!
# External costs of executions

A cost is a function of two successive configurations, independently of the machine model.
`runCost` accumulates costs along deterministic execution.
-/

@[expose] public section

namespace Complexity.Transition

variable {α : Type*}

/-- Accumulate an external step cost along a deterministic execution. -/
def runCost (f : α → α) (w : α → α → ℕ) : ℕ → α → ℕ
  | 0, _ => 0
  | n + 1, a => w a (f a) + runCost f w n (f a)

@[simp] theorem runCost_zero (f : α → α) (w : α → α → ℕ) (a : α) :
    runCost f w 0 a = 0 := rfl

theorem runCost_succ (f : α → α) (w : α → α → ℕ) (n : ℕ) (a : α) :
    runCost f w (n + 1) a = w a (f a) + runCost f w n (f a) := rfl

@[simp] theorem runCost_const (f : α → α) (cost n : ℕ) (a : α) :
    runCost f (fun _ _ ↦ cost) n a = n * cost := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => simp [runCost_succ, ih, Nat.succ_mul, Nat.add_comm]

theorem runCost_add (f : α → α) (w : α → α → ℕ) (s t : ℕ) (a : α) :
    runCost f w (s + t) a =
      runCost f w s a + runCost f w t ((runN (m := Id) (pure ∘ f) s a).run) := by
  induction s generalizing a with
  | zero =>
    simp only [Nat.zero_add, runCost_zero, runN_zero]
    rfl
  | succ s ih =>
    rw [Nat.succ_add]
    change w a (f a) + runCost f w (s + t) (f a) =
      (w a (f a) + runCost f w s (f a)) + runCost f w t ((runN (m := Id) (pure ∘ f) s (f a)).run)
    rw [ih, Nat.add_assoc]

theorem runCost_succ' (f : α → α) (w : α → α → ℕ) (n : ℕ) (a : α) :
    runCost f w (n + 1) a = runCost f w n a +
      w ((runN (m := Id) (pure ∘ f) n a).run)
        ((runN (m := Id) (pure ∘ f) (n + 1) a).run) := by
  rw [runCost_add, runN_succ']
  rfl

theorem runCost_mono (f : α → α) (w : α → α → ℕ) (a : α)
    {s t : ℕ} (h : s ≤ t) : runCost f w s a ≤ runCost f w t a := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [runCost_add]
  exact Nat.le_add_right _ _

theorem runCost_le_runCost (f : α → α) {w v : α → α → ℕ}
    (h : ∀ a, w a (f a) ≤ v a (f a)) (n : ℕ) (a : α) :
    runCost f w n a ≤ runCost f v n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact Nat.add_le_add (h a) (ih (f a))

/-- A potential whose increase is paid for at each step is bounded by cumulative cost. -/
theorem potential_runN_le (f : α → α) (w : α → α → ℕ) (p : α → ℕ)
    (h : ∀ a, p (f a) ≤ p a + w a (f a)) (n : ℕ) (a : α) :
    p ((runN (m := Id) (pure ∘ f) n a).run) ≤ p a + runCost f w n a := by
  induction n generalizing a with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h₁ := ih (f a)
    have h₂ := h a
    change p ((runN (m := Id) (pure ∘ f) n (f a)).run) ≤ p a + (w a (f a) + runCost f w n (f a))
    omega

/-- The same bound holds at every earlier execution prefix. -/
theorem potential_runN_le_of_le (f : α → α) (w : α → α → ℕ) (p : α → ℕ)
    (h : ∀ a, p (f a) ≤ p a + w a (f a)) {s t : ℕ} (ht : s ≤ t) (a : α) :
    p ((runN (m := Id) (pure ∘ f) s a).run) ≤ p a + runCost f w t a :=
  Nat.le_trans (potential_runN_le f w p h s a)
    (Nat.add_le_add_left (runCost_mono f w a ht) _)

end Complexity.Transition
