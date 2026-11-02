/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Asymptotics.Nat
public import Complexity.Encoding.Bool
public import Complexity.Models.TreeMachine.Deterministic

/-!
# Function complexity for tree machines

The input and output use register zero; every other register starts empty.
Input size counts tree nodes, including leaves. Time counts either active transitions
or cumulative instruction size charges; both models use peak expanded register size for space.
A single finite machine must handle every valid input.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β : Type*} {k : ℕ} {Q : Type*} [NeZero k]

/-- Destination-size charges also control the size of an intermediate output code. -/
theorem ComputesWithin.output_size_le {M : TreeMachine Id k Q}
    {a b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) : b.size ≤ a.size + k + t := by
  exact h.output_size_le_mass_add_time.trans
    (Nat.add_le_add_right (Cfg.mass_init_le a) t)

variable [Encoding Tree α] [Encoding Tree β]

/-- Finite tree machines with input and output register zero. Time sums destination
sizes; space is the maximum total expanded register size. -/
@[simps inputSize]
def _root_.Complexity.TimeSpaceModel.sizeCostTree : TimeSpaceModel Id Tree where
  inputSize := Tree.size
  behaviors := {R | ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q)
      (M : TreeMachine Id k Q), R = fun a result => M.ComputesWithin a result.run}
  budget_mono := by
    rintro R ⟨k, hk, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Finite tree machines with unit transition time and peak expanded-tree space. -/
def _root_.Complexity.TimeSpaceModel.tree : TimeSpaceModel Id Tree where
  inputSize := Tree.size
  behaviors := {R | ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q)
      (M : TreeMachine Id k Q), R = fun a result => M.ComputesInUnitTimeAndSpace a result.run}
  budget_mono := by
    rintro R ⟨k, hk, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

section InputBudgets

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

/-- Size-charged time and expanded-tree space, indexed by the input value. -/
def Computes (M : TreeMachine Id k Q) (f : α → β) (t s : α → ℕ) : Prop :=
  Encoding.Computes f fun value input output =>
    M.ComputesWithin input output (t value) (s value)

theorem computableWithin_iff {f : α → β} {t s : α → ℕ} :
    TimeSpaceModel.sizeCostTree.ComputableWithin f t s ↔
      ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q)
        (M : TreeMachine Id k Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩
    exact ⟨k, hk, Q, hQ, M, h⟩
  · rintro ⟨k, hk, Q, hQ, M, h⟩
    exact ⟨_, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩

variable {f : α → β} {t s t' s' : α → ℕ}

theorem Computes.mono {M : TreeMachine Id k Q}
    (h : Computes M f t s) (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    Computes M f t' s' :=
  Encoding.Computes.mono h (fun hc => hc.mono (ht _) (hs _))

theorem Computes.computableWithin {Q : Type} [Finite Q]
    {M : TreeMachine Id k Q} (h : Computes M f t s) :
    TimeSpaceModel.sizeCostTree.ComputableWithin f t s :=
  computableWithin_iff.mpr ⟨k, inferInstance, Q, inferInstance, M, h⟩

/-- Changing the time charge keeps the same machine, valid codes, and joint budgets. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithinByCode.toUnitTime {t s : α → Tree → ℕ}
    (h : TimeSpaceModel.sizeCostTree.ComputableWithinByCode f t s) :
    TimeSpaceModel.tree.ComputableWithinByCode f t s := by
  obtain ⟨R, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩ := h
  exact ⟨_, ⟨k, hk, Q, hQ, M, rfl⟩, h.mono (fun hc => hc.toUnitTime)⟩

/-- Size charging uses the same machine's peak space to bound each unit-time action. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithinByCode.toSizeCost {t s : α → Tree → ℕ}
    (h : TimeSpaceModel.tree.ComputableWithinByCode f t s) :
    TimeSpaceModel.sizeCostTree.ComputableWithinByCode f
      (fun a src => t a src * s a src) s := by
  obtain ⟨R, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩ := h
  exact ⟨_, ⟨k, hk, Q, hQ, M, rfl⟩, h.mono (fun hc => hc.toSizeCost)⟩

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toUnitTime
    (h : TimeSpaceModel.sizeCostTree.ComputableWithin f t s) :
    TimeSpaceModel.tree.ComputableWithin f t s :=
  TimeSpaceModel.ComputableWithinByCode.toUnitTime h

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toSizeCost
    (h : TimeSpaceModel.tree.ComputableWithin f t s) :
    TimeSpaceModel.sizeCostTree.ComputableWithin f (fun a => t a * s a) s :=
  TimeSpaceModel.ComputableWithinByCode.toSizeCost h

theorem _root_.Complexity.TimeSpaceModel.ComputableInO.toUnitTime
    (h : TimeSpaceModel.sizeCostTree.ComputableInO f t s) :
    TimeSpaceModel.tree.ComputableInO f t s := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨u, v, TimeSpaceModel.ComputableWithin.toUnitTime h, hu, hv⟩

theorem _root_.Complexity.TimeSpaceModel.ComputableInO.toSizeCost
    (h : TimeSpaceModel.tree.ComputableInO f t s) :
    TimeSpaceModel.sizeCostTree.ComputableInO f (fun a => t a * s a) s := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨_, _, TimeSpaceModel.ComputableWithin.toSizeCost h, hu.mul hv, hv⟩

end InputBudgets

end Complexity.TreeMachine
