/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic
public import Complexity.Resources.StackMachine.TuringMachine
public import Mathlib.Analysis.Asymptotics.Ring

/-! # Time complexity preserved by the stack-to-tape simulation -/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- A constant-factor time simulation preserves every asymptotic time class. -/
theorem ftime_subset_tm (T : ℕ → ℕ) :
    FTIME (α := α) (β := β) timeSpaceModel T ⊆ FTIME TM.timeSpaceModel T := by
  rintro f ⟨t, h, ht⟩
  refine ⟨_, computableInTime_toTM h, ?_⟩
  simpa [IsBigO, Nat.cast_mul] using Asymptotics.IsBigO.const_mul_left ht (2 : ℝ)

/-- Polynomial-time stack computations are polynomial-time Turing computations. -/
theorem fp_subset_tm :
    FP (α := α) (β := β) timeSpaceModel ⊆ FP TM.timeSpaceModel :=
  Set.iUnion_mono fun _ ↦ ftime_subset_tm _

end Complexity.StackMachine
