/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeSimulation
public import Complexity.Classes.StackMachine.TuringMachine

/-! # Polynomial tree-to-Turing simulation through stack machines -/

@[expose] public section

namespace Complexity.TreeMachine

/-- Default serialized tree codes transport polynomial time through stack machines. -/
theorem fp_subset_tm {α β : Type*} [Encoding Tree α] [Encoding Tree β] :
    FP (α := α) (β := β) .sizeCostTree ⊆ FP .tm :=
  fp_subset_stack.trans StackMachine.fp_eq_tm.subset

end Complexity.TreeMachine
