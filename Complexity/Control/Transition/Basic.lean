/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Fin.Tuple.Basic
public import Complexity.Control.MonadReturns

/-!
# Bounded execution of monadic transitions

Execution only requires `Monad`. Composition laws require `LawfulMonad`.
Branch restrictions, acceptance, and resource interpretations belong to concrete models.
-/

@[expose] public section

universe u

namespace Complexity.Transition

variable {m : Type u → Type*} [Monad m] {α : Type u}

/-- Execute a transition exactly `n` times. -/
def runN (f : α → m α) : ℕ → α → m α
  | 0, a => pure a
  | n + 1, a => f a >>= runN f n

@[simp]
theorem runN_zero (f : α → m α) (a : α) : runN f 0 a = pure a := rfl

theorem runN_succ (f : α → m α) (n : ℕ) (a : α) :
    runN f (n + 1) a = f a >>= runN f n := rfl

section Lawful

variable [LawfulMonad m]

theorem runN_add (f : α → m α) (n k : ℕ) (a : α) :
    runN f (n + k) a = runN f n a >>= runN f k := by
  induction n generalizing a with
  | zero => simp [runN]
  | succ n ih =>
    simp only [Nat.succ_add, runN, bind_assoc]
    congr 1
    funext b
    exact ih b

theorem runN_succ' (f : α → m α) (n : ℕ) (a : α) :
    runN f (n + 1) a = runN f n a >>= f := by
  simpa [runN] using runN_add f n 1 a

theorem runN_of_fixed (f : α → m α) {a : α} (h : f a = pure a) (n : ℕ) :
    runN f n a = pure a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runN, h, ih]

/-- A step-indexed property preserved by every step holds for every value the iteration can
return. -/
theorem forall_mem_runN [MonadReturns m] (f : α → m α) {P : ℕ → α → Prop} {a : α} (ha : P 0 a)
    (hstep : ∀ k b, P k b → ∀ c ∈ returns (f b), P (k + 1) c) (n : ℕ) :
    ∀ b ∈ returns (runN f n a), P n b := by
  induction n with
  | zero => exact fun b hb ↦ mem_returns_pure_iff.mp hb ▸ ha
  | succ n ih =>
    intro c hc
    rw [runN_succ', mem_returns_bind_iff] at hc
    obtain ⟨b, hb, hc⟩ := hc
    exact hstep n b (ih b hb) c hc

end Lawful

/-- If one step can return exactly the successors `step a i`, then `n` steps can return exactly
the endpoints of the label sequences of length `n`. -/
theorem mem_returns_runN_iff [MonadReturns m] {ι : Type*} (f : α → m α) (step : α → ι → α)
    (hstep : ∀ a b, b ∈ returns (f a) ↔ ∃ i, step a i = b) (a b : α) (n : ℕ) :
    b ∈ returns (runN f n a) ↔ ∃ is : Fin n → ι, (List.ofFn is).foldl step a = b := by
  induction n generalizing a with
  | zero => simp [mem_returns_pure_iff, eq_comm]
  | succ n ih =>
    simp only [runN_succ, mem_returns_bind_iff, hstep, ih, Fin.exists_fin_succ_pi, List.ofFn_succ,
      Fin.cons_zero, Fin.cons_succ, List.foldl_cons, exists_exists_eq_and]

theorem runN_id (f : α → α) (n : ℕ) (a : α) : (runN (m := Id) (pure ∘ f) n a).run = f^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact (ih (f a)).trans (Function.iterate_succ_apply f n a).symm

end Complexity.Transition
