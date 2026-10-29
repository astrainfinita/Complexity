/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Deterministic
public import Complexity.Resources.TreeMachine.Basic

/-! # Comparing unit-time and size-charged tree complexity classes -/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

theorem fdtisp_sizeCost_subset_unitTime (T S : ℕ → ℕ) :
    FDTISP (α := α) (β := β) .sizeCostTree T S ⊆ FDTISP .tree T S := by
  rintro f ⟨t, s, h, ht, hs⟩
  have h : TimeSpaceModel.tree.ComputableWithSizeBudgets f t s :=
    TimeSpaceModel.ComputableWithCodeBudgets.toUnitTime h
  exact h.mem_fdtisp_of_dominated ht hs

/-- Size charging multiplies the unit-time bound by the space bound. -/
theorem fdtisp_unitTime_subset_sizeCost (T S : ℕ → ℕ) :
    FDTISP (α := α) (β := β) .tree T S ⊆ FDTISP .sizeCostTree (fun n ↦ T n * S n) S := by
  rintro f ⟨t, s, h, ht, hs⟩
  have h : TimeSpaceModel.sizeCostTree.ComputableWithSizeBudgets f (fun n => t n * s n) s :=
    TimeSpaceModel.ComputableWithCodeBudgets.toSizeCost h
  exact h.mem_fdtisp_of_dominated (ht.mul hs) hs

/-- Changing action charges preserves every expanded-tree space class. -/
theorem fdspace_eq_sizeCost (S : ℕ → ℕ) :
    FDSPACE (α := α) (β := β) .tree S = FDSPACE .sizeCostTree S := by
  apply Set.Subset.antisymm
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FDTISP.subset_space (fdtisp_unitTime_subset_sizeCost t S
      (h.mem_fdtisp_of_dominated (DominatedAtTop.refl _) hs))
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FDTISP.subset_space (fdtisp_sizeCost_subset_unitTime t S
      (h.mem_fdtisp_of_dominated (DominatedAtTop.refl _) hs))

theorem dspace_eq_sizeCost (S : ℕ → ℕ) :
    DSPACE (α := α) .tree S = DSPACE .sizeCostTree S :=
  congrArg DecisionClass (fdspace_eq_sizeCost S)

end Complexity.TreeMachine
