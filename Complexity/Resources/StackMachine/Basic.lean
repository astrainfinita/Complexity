/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.RawWord
public import Complexity.Models.StackMachine.Deterministic

/-!
# Time and space complexity on stack machines

Finite machines act on bit strings. Time counts transitions; space is the largest total
number of symbols on the work stacks, excluding the read-only input and append-only output.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- Finite stack machines with transition time and peak work-stack space. -/
def _root_.Complexity.TimeSpaceModel.stack : TimeSpaceModel Id (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : StackMachine Id κ Bool Q),
      R = fun xs result ↦ M.ComputesWithin xs.toList result.run.toList}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- One stack machine with budgets depending on its input value. -/
def Computes {κ Q : Type*} [Fintype κ] (M : StackMachine Id κ Bool Q)
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

theorem Computes.mono {κ Q : Type*} [Fintype κ] {M : StackMachine Id κ Bool Q}
    {f : α → β} {t s t' s' : α → ℕ} (h : Computes M f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) : Computes M f t' s' :=
  Encoding.Computes.mono h (fun hc => hc.mono (ht _) (hs _))

theorem Computes.computableWithin {κ Q : Type} [Fintype κ] [Finite Q]
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : α → ℕ}
    (h : Computes M f t s) : TimeSpaceModel.stack.ComputableWithin f t s :=
  computableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.StackMachine
