/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic
public import Complexity.Resources.TreeMachine.StackMachine
public import Mathlib.Data.Fintype.EquivFin

/-! # Polynomial tree computations on serialized tree codes

The tree-to-stack compiler preserves the chosen tree encodings at both boundaries.
Code length equals tree size, so its linear resource bounds transport polynomial time
uniformly, without per-type encoding conversions.
-/

@[expose] public section

namespace Complexity

namespace TreeMachine

open TreeMachine.Simulation

/-- Default raw codes serialize the chosen tree encodings, so the simulation
applies uniformly to all represented data types. -/
theorem fp_subset_stack {α β : Type*} [Encoding Tree α] [Encoding Tree β] :
    FP (α := α) (β := β) .sizeCostTree ⊆ FP .stack := by
  classical
  intro f hf
  obtain ⟨p, s, h⟩ := FP.exists_polynomial_bound hf
  obtain ⟨k, hk, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  let : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  let q : Polynomial ℕ := 43 * p + 12 * Polynomial.X + Polynomial.C (6 * k + 8)
  have hq (n : ℕ) : timeBound k n (p.eval n) = q.eval n := by simp [timeBound, q]; omega
  obtain ⟨b, hb⟩ := IsBigO.exists_pow q
  exact FP.ftime_subset b ⟨_, ⟨_, h.toStack.computableInTimeAndSpace⟩,
    (IsBigO.of_le fun n ↦ (hq n).le).trans hb⟩

end TreeMachine

end Complexity
