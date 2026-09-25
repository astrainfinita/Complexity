/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine
public import Complexity.Asymptotics.Basic

/-!
# Asymptotic function complexity for tree machines

The witnessing resource functions bound every valid input. Only comparison with
the requested asymptotic bounds ignores finitely many input sizes. Simultaneous
time and space bounds are witnessed by the same machine.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

/-- Computability with cumulative destination-size cost in `O(T)`. -/
def ComputableInTimeO (f : α → β) (T : ℕ → ℕ) : Prop :=
  ∃ t, ComputableInTime f t ∧ IsBigO t T

/-- Computability with expanded-tree space in `O(S)`. -/
def ComputableInSpaceO (f : α → β) (S : ℕ → ℕ) : Prop :=
  ∃ s, ComputableInSpace f s ∧ IsBigO s S

/-- A single machine computes the function with time in `O(T)` and space in `O(S)`. -/
def ComputableInTimeAndSpaceO (f : α → β) (T S : ℕ → ℕ) : Prop :=
  ∃ t s, ComputableInTimeAndSpace f t s ∧ IsBigO t T ∧ IsBigO s S

variable {f : α → β} {t s T S T' S' : ℕ → ℕ}

theorem ComputableInTime.computableInTimeO (h : ComputableInTime f t) :
    ComputableInTimeO f t :=
  ⟨t, h, IsBigO.refl t⟩

theorem ComputableInSpace.computableInSpaceO (h : ComputableInSpace f s) :
    ComputableInSpaceO f s :=
  ⟨s, h, IsBigO.refl s⟩

theorem ComputableInTimeAndSpace.computableInTimeAndSpaceO
    (h : ComputableInTimeAndSpace f t s) : ComputableInTimeAndSpaceO f t s :=
  ⟨t, s, h, IsBigO.refl t, IsBigO.refl s⟩

theorem ComputableInTimeO.mono (h : ComputableInTimeO f T) (hT : IsBigO T T') :
    ComputableInTimeO f T' := by
  obtain ⟨t, h, ht⟩ := h
  exact ⟨t, h, ht.trans hT⟩

theorem ComputableInSpaceO.mono (h : ComputableInSpaceO f S) (hS : IsBigO S S') :
    ComputableInSpaceO f S' := by
  obtain ⟨s, h, hs⟩ := h
  exact ⟨s, h, hs.trans hS⟩

theorem ComputableInTimeAndSpaceO.mono (h : ComputableInTimeAndSpaceO f T S)
    (hT : IsBigO T T') (hS : IsBigO S S') : ComputableInTimeAndSpaceO f T' S' := by
  obtain ⟨t, s, h, ht, hs⟩ := h
  exact ⟨t, s, h, ht.trans hT, hs.trans hS⟩

theorem ComputableInTimeAndSpaceO.computableInTimeO
    (h : ComputableInTimeAndSpaceO f T S) : ComputableInTimeO f T := by
  obtain ⟨t, s, h, ht, _⟩ := h
  exact ⟨t, h.computableInTime, ht⟩

theorem ComputableInTimeAndSpaceO.computableInSpaceO
    (h : ComputableInTimeAndSpaceO f T S) : ComputableInSpaceO f S := by
  obtain ⟨t, s, h, _, hs⟩ := h
  exact ⟨s, h.computableInSpace, hs⟩

end Complexity.TreeMachine
