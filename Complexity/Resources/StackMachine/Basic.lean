/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.RawWord
public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Control.BinaryChoice.Basic

/-!
# Time and space complexity on stack machines

Finite machines act on bit strings. Time counts transitions; space is the largest total
number of symbols on the work stacks, excluding the read-only input and append-only output.

The model is stated once for every choice shape and interpretation, `TimeSpaceModel.stackWith`;
`TimeSpaceModel.stack` is its deterministic instance and `TimeSpaceModel.nstack` its instance with
binary choices on `Multiset`.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- Finite stack machines on bit strings, with choices of shape `F` interpreted in `m`,
transition time and peak work-stack space. Each behavior is realized by one machine for all
inputs: on every history both measurements stay within budget, and at some step every result has
halted with the corresponding output. -/
def _root_.Complexity.TimeSpaceModel.stackWith (F : Type → Type*) (m : Type → Type*) [Monad m]
    [MonadLiftT F m] [MonadReturns m] : TimeSpaceModel m (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : StackMachine F κ Bool Q), R = fun (xs : RawWord Bool) ys =>
        M.ComputesWithinWith m xs.toList (RawWord.toList <$> ys)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Finite stack machines with transition time and peak work-stack space. This is the
deterministic instance of `TimeSpaceModel.stackWith`. -/
@[simps! inputSize]
def _root_.Complexity.TimeSpaceModel.stack : TimeSpaceModel Id (RawWord Bool) :=
  TimeSpaceModel.stackWith Id Id

/-- Finite binary-choice stack machines, retaining all branch outputs and their multiplicities.
Resource bounds cover every branch, including rejecting branches. The outputs are read at any step
by which every branch has halted. This is the instance of `TimeSpaceModel.stackWith` with binary
choices interpreted in `Multiset`. -/
def _root_.Complexity.TimeSpaceModel.nstack : TimeSpaceModel Multiset (RawWord Bool) :=
  TimeSpaceModel.stackWith BinaryChoice Multiset

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- One stack machine with budgets depending on its input value. -/
def Computes {κ Q : Type} [Fintype κ] (M : StackMachine Id κ Bool Q)
    (f : α → β) (t s : α → ℕ) : Prop :=
  Encoding.Computes f fun value (input output : RawWord Bool) =>
    M.ComputesWithin input.toList output.toList (t value) (s value)

theorem computableWithin_iff {f : α → β} {t s : α → ℕ} :
    TimeSpaceModel.stack.ComputableWithin f t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : StackMachine Id κ Bool Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    exact ⟨κ, hκ, Q, hQ, M, h⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    exact ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩

theorem Computes.mono {κ Q : Type} [Fintype κ] {M : StackMachine Id κ Bool Q}
    {f : α → β} {t s t' s' : α → ℕ} (h : Computes M f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) : Computes M f t' s' :=
  Encoding.Computes.mono h (fun hc => hc.mono (ht _) (hs _))

theorem Computes.computableWithin {κ Q : Type} [Fintype κ] [Finite Q]
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : α → ℕ}
    (h : Computes M f t s) : TimeSpaceModel.stack.ComputableWithin f t s :=
  computableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.StackMachine
