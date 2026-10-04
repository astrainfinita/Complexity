/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.Bool
public import Complexity.Models.TreeMachine.Deterministic

/-!
# Function complexity for tree machines

The input and output use register zero; every other register starts empty.
Input size is the size of the actual tree representation, including leaves. Time
uses the machine's cumulative destination-size charge, and space uses its maximum total
expanded register size. A single finite machine must handle every valid input.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β : Type*} {k : ℕ} {Q : Type*} [NeZero k]

/-- Destination-size charges also control the size of an intermediate output code. -/
theorem ComputesInTimeAndSpace.output_size_le {M : TreeMachine Id k Q}
    {a b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) : b.size ≤ a.size + k + t := by
  exact h.output_size_le_mass_add_time.trans
    (Nat.add_le_add_right (mass_input_le M a) t)

variable [Encoding Tree α] [Encoding Tree β]

/-- A tree machine computes a function between encoded types within the given
destination-size time and expanded-tree space bounds. -/
def Computes (M : TreeMachine Id k Q) (f : α → β)
    (t s : ℕ → ℕ) : Prop :=
  Encoding.Computes (fun a b => M.ComputesInTimeAndSpace a b)
    Tree.size f t s

/-- Finite tree machines with input and output register zero. Time sums destination
sizes; space is the maximum total expanded register size. -/
def _root_.Complexity.TimeSpaceModel.sizeCostTree : TimeSpaceModel Id Tree where
  inputSize := Tree.size
  behaviors := {R | ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q)
      (M : TreeMachine Id k Q), R = fun a result => M.ComputesInTimeAndSpace a result.run}
  budget_mono := by
    rintro R ⟨k, hk, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Recover the single finite machine realizing the abstract resource behavior. -/
theorem computableInTimeAndSpace_iff {f : α → β} {t s : ℕ → ℕ} :
    TimeSpaceModel.sizeCostTree.ComputableInTimeAndSpace f t s ↔
      ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q)
        (M : TreeMachine Id k Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩
    exact ⟨k, hk, Q, hQ, M, h⟩
  · rintro ⟨k, hk, Q, hQ, M, h⟩
    exact ⟨_, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩

variable {f : α → β} {t s t' s' : ℕ → ℕ}

theorem Computes.mono {M : TreeMachine Id k Q}
    (h : Computes M f t s) (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    Computes M f t' s' :=
  Encoding.Computes.mono h (fun h ht hs ↦ h.mono ht hs) ht hs

theorem Computes.computableInTimeAndSpace {Q : Type} [Finite Q]
    {M : TreeMachine Id k Q} (h : Computes M f t s) :
    TimeSpaceModel.sizeCostTree.ComputableInTimeAndSpace f t s :=
  computableInTimeAndSpace_iff.mpr ⟨k, inferInstance, Q, inferInstance, M, h⟩

end Complexity.TreeMachine
