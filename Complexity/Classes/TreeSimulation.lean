/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic
public import Complexity.Resources.TreeMachine.StackMachine

/-! # Tree computations on serialized tree codes

The tree-to-stack compiler preserves the chosen tree encodings at both boundaries.
Code length equals tree size, so its linear resource bounds transport simultaneous
bounds and polynomial time uniformly, without per-type encoding conversions.
-/

@[expose] public section

namespace Complexity

namespace TreeMachine

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

/-- Serialization keeps both asymptotic bounds and adds the cost of loading the input. -/
theorem fdtisp_subset_stack (T S : ℕ → ℕ) :
    FDTISP (α := α) (β := β) .sizeCostTree T S ⊆ FDTISP .stack (fun n => T n + n) S := by
  rintro f ⟨t, s, h, ht, hs⟩
  obtain ⟨c, h⟩ := TimeSpaceModel.ComputableWithinBySize.toStack_of_tree h
  exact h.mem_fdtisp_of_dominated ((ht.add (DominatedAtTop.refl _)).const_mul_left c)
    (hs.const_mul_left c)

/-- Default raw codes serialize the chosen tree encodings, so the simulation
applies uniformly to all represented data types. -/
theorem fp_subset_stack : FP (α := α) (β := β) .sizeCostTree ⊆ FP .stack := by
  intro f hf
  obtain ⟨t, s, h, ht⟩ := FP.mem_iff_isPoly.1 hf
  exact FP.of_isPoly (FDTISP.subset_time (fdtisp_subset_stack t s h.mem_fdtisp)) (ht.add .refl)

end TreeMachine

end Complexity
