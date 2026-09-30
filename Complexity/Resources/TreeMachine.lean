/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Basic
public import Complexity.Encoding.Tree
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
  Complexity.Computes (fun a b => M.ComputesInTimeAndSpace a b)
    Tree.size f t s

/-- A function has the stated bounds on some finite tree machine with fixed
input and output register zero. -/
def ComputableInTimeAndSpace (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (Q : Type) (_ : Finite Q) (M : TreeMachine Id k Q),
    Computes M f t s

/-- Some finite tree machine computes the function within the time bound. -/
def ComputableInTime (f : α → β) (t : ℕ → ℕ) : Prop :=
  ∃ s, ComputableInTimeAndSpace f t s

/-- Some finite tree machine computes the function within the space bound. -/
def ComputableInSpace (f : α → β) (s : ℕ → ℕ) : Prop :=
  ∃ t, ComputableInTimeAndSpace f t s

variable {f : α → β} {t s t' s' : ℕ → ℕ}

theorem Computes.mono {M : TreeMachine Id k Q}
    (h : Computes M f t s) (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    Computes M f t' s' :=
  Complexity.Computes.mono h (fun h ht hs => Controller.computes_mono h ht hs) ht hs

theorem Computes.computableInTimeAndSpace {Q : Type} [Finite Q]
    {M : TreeMachine Id k Q} (h : Computes M f t s) :
    ComputableInTimeAndSpace f t s :=
  ⟨k, inferInstance, Q, inferInstance, M, h⟩

theorem ComputableInTimeAndSpace.mono (h : ComputableInTimeAndSpace f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    ComputableInTimeAndSpace f t' s' := by
  obtain ⟨k, hk, Q, hQ, M, h⟩ := h
  exact ⟨k, hk, Q, hQ, M, h.mono ht hs⟩

theorem ComputableInTimeAndSpace.computableInTime (h : ComputableInTimeAndSpace f t s) :
    ComputableInTime f t :=
  ⟨s, h⟩

theorem ComputableInTimeAndSpace.computableInSpace (h : ComputableInTimeAndSpace f t s) :
    ComputableInSpace f s :=
  ⟨t, h⟩

theorem ComputableInTime.mono (h : ComputableInTime f t) (ht : ∀ n, t n ≤ t' n) :
    ComputableInTime f t' := by
  obtain ⟨s, h⟩ := h
  exact ⟨s, h.mono ht (fun _ => le_rfl)⟩

theorem ComputableInSpace.mono (h : ComputableInSpace f s) (hs : ∀ n, s n ≤ s' n) :
    ComputableInSpace f s' := by
  obtain ⟨t, h⟩ := h
  exact ⟨t, h.mono (fun _ => le_rfl) hs⟩

end Complexity.TreeMachine
