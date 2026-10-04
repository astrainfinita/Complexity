/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Deterministic
public import Complexity.Resources.TreeMachine.Basic
public import Mathlib.Analysis.Asymptotics.Ring

/-! # Comparing unit-time and size-charged tree complexity classes -/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

theorem ftisp_sizeCost_subset_unitTime (T S : ℕ → ℕ) :
    FTISP (α := α) (β := β) .sizeCostTree T S ⊆ FTISP .tree T S := by
  rintro f ⟨t, s, h, ht, hs⟩
  exact ⟨t, s, computableInTimeAndSpace_toUnitTime h, ht, hs⟩

/-- Charging destination sizes multiplies the unit-time bound by the space bound. -/
theorem ftisp_unitTime_subset_sizeCost (T S : ℕ → ℕ) :
    FTISP (α := α) (β := β) .tree T S ⊆ FTISP .sizeCostTree (fun n ↦ T n * S n) S := by
  rintro f ⟨t, s, h, ht, hs⟩
  refine ⟨_, s, computableInTimeAndSpace_toSizeCost h, ?_, hs⟩
  simpa only [IsBigO, Nat.cast_mul] using Asymptotics.IsBigO.mul ht hs

/-- Changing action charges preserves every expanded-tree space class. -/
theorem fspace_eq_sizeCost (S : ℕ → ℕ) :
    FSPACE (α := α) (β := β) .tree S = FSPACE .sizeCostTree S := by
  apply Set.Subset.antisymm
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact ⟨s, ⟨_, computableInTimeAndSpace_toSizeCost h⟩, hs⟩
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact ⟨s, ⟨t, computableInTimeAndSpace_toUnitTime h⟩, hs⟩

theorem dspace_eq_sizeCost (S : ℕ → ℕ) :
    DSPACE (α := α) .tree S = DSPACE .sizeCostTree S :=
  congrArg DecisionClass (fspace_eq_sizeCost S)

end Complexity.TreeMachine
