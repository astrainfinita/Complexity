/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Bounded execution of monadic transitions

Execution only requires `Monad`. Composition laws require `LawfulMonad`.
Branch restrictions, acceptance, and resource interpretations belong to concrete models.
Traces record semantic history; they are not stored by the machine being studied.
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

/-- Record the initial configuration and each of the `n` successors. -/
def runTrace (f : α → m α) : ℕ → α → m (List α)
  | 0, a => pure [a]
  | n + 1, a => do
    let b ← f a
    let bs ← runTrace f n b
    pure (a :: bs)

@[simp]
theorem runTrace_zero (f : α → m α) (a : α) : runTrace f 0 a = pure [a] := rfl

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

/-- The last configuration of an execution trace agrees with bounded execution. -/
theorem getLastD_runTrace (f : α → m α) (n : ℕ) (a b : α) :
    (fun as ↦ as.getLastD b) <$> runTrace f n a = runN f n a := by
  induction n generalizing a b with
  | zero => simp [runTrace, runN]
  | succ n ih =>
    simp only [runTrace, runN, map_bind, bind_pure_comp]
    congr 1
    funext c
    simpa only [Functor.map_map, Function.comp_def, List.getLastD_cons] using ih c a

end Lawful

theorem runN_id (f : α → α) (n : ℕ) (a : α) : (runN (m := Id) (pure ∘ f) n a).run = f^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact (ih (f a)).trans (Function.iterate_succ_apply f n a).symm

end Complexity.Transition
