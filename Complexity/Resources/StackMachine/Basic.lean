/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.Bool
public import Complexity.Models.StackMachine.Deterministic

/-!
# Time and space complexity on stack machines

Finite machines act on bit strings. Time counts transitions; space is the largest total
number of symbols on the work stacks, excluding the read-only input and append-only output.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- One stack machine computes the function on every valid bit-string encoding. -/
def Computes {κ Q : Type*} [Fintype κ] (M : StackMachine Id κ Bool Q)
    (f : α → β) (t s : ℕ → ℕ) : Prop :=
  Complexity.Computes (fun xs ys ↦ M.ComputesInTimeAndSpace xs ys) List.length f t s

/-- Finite stack machines with transition time and peak work-stack space. -/
def timeSpaceModel : TimeSpaceModel Id (List Bool) where
  inputSize := List.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : StackMachine Id κ Bool Q), R = fun xs result ↦ M.ComputesInTimeAndSpace xs result.run}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Recover the single finite machine realizing the abstract resource behavior. -/
theorem computableInTimeAndSpace_iff {f : α → β} {t s : ℕ → ℕ} :
    timeSpaceModel.ComputableInTimeAndSpace f t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : StackMachine Id κ Bool Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    exact ⟨κ, hκ, Q, hQ, M, h⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    exact ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩

theorem Computes.mono {κ Q : Type*} [Fintype κ] {M : StackMachine Id κ Bool Q}
    {f : α → β} {t s t' s' : ℕ → ℕ} (h : Computes M f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) : Computes M f t' s' :=
  Complexity.Computes.mono h (fun h ht hs ↦ h.mono ht hs) ht hs

theorem Computes.computableInTimeAndSpace {κ Q : Type} [Fintype κ] [Finite Q]
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) : timeSpaceModel.ComputableInTimeAndSpace f t s :=
  computableInTimeAndSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end Complexity.StackMachine
