/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TuringMachine
public import Complexity.Asymptotics.Basic

/-!
# Asymptotic function complexity on Turing machines

The `O` variants retain an exact resource function and one fixed finite machine.
Only the comparison with the requested bound is eventual: termination and
correctness are still required on every valid input, including short inputs.
The simultaneous variant retains one machine satisfying both bounds.
-/

@[expose] public section

namespace Complexity.TM

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- Compute a function in time `O(T(n))`, measured on the actual input code. -/
def ComputableInTimeO (f : α → β) (T : ℕ → ℕ) : Prop :=
  ∃ t, ComputableInTime f t ∧ IsBigO t T

/-- Compute a function in work space `O(S(n))`, with termination on all valid inputs. -/
def ComputableInSpaceO (f : α → β) (S : ℕ → ℕ) : Prop :=
  ∃ s, ComputableInSpace f s ∧ IsBigO s S

/-- One finite machine computes a function in time `O(T(n))` and space `O(S(n))`. -/
def ComputableInTimeAndSpaceO (f : α → β) (T S : ℕ → ℕ) : Prop :=
  ∃ t s, ComputableInTimeAndSpace f t s ∧ IsBigO t T ∧ IsBigO s S

variable {f : α → β} {t s T S T' S' : ℕ → ℕ}

theorem ComputableInTime.computableInTimeO (h : ComputableInTime f t) :
    ComputableInTimeO f t := ⟨t, h, IsBigO.refl t⟩

theorem ComputableInSpace.computableInSpaceO (h : ComputableInSpace f s) :
    ComputableInSpaceO f s := ⟨s, h, IsBigO.refl s⟩

theorem ComputableInTimeAndSpace.computableInTimeAndSpaceO
    (h : ComputableInTimeAndSpace f t s) : ComputableInTimeAndSpaceO f t s :=
  ⟨t, s, h, IsBigO.refl t, IsBigO.refl s⟩

theorem ComputableInTimeO.mono (h : ComputableInTimeO f T) (hT : IsBigO T T') :
    ComputableInTimeO f T' := by
  obtain ⟨t, ht, hT₀⟩ := h
  exact ⟨t, ht, hT₀.trans hT⟩

theorem ComputableInSpaceO.mono (h : ComputableInSpaceO f S) (hS : IsBigO S S') :
    ComputableInSpaceO f S' := by
  obtain ⟨s, hs, hS₀⟩ := h
  exact ⟨s, hs, hS₀.trans hS⟩

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

end Complexity.TM
