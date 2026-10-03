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

/-- Tree computations on list-tree representations yield Turing computations on raw bits. -/
theorem fp_subset_tm_comp {α β : Type*} [e : Encoding (List Bool) α]
    [d : Encoding (List Bool) β] :
    @FP Tree α β (bitListEncoding.toEncoding.comp e) (bitListEncoding.toEncoding.comp d)
      timeSpaceModel ⊆ FP TM.timeSpaceModel :=
  fp_subset_stack_comp.trans StackMachine.fp_subset_tm

/-- Encoding conversions on tree machines suffice for the composite simulation. -/
theorem fp_subset_tm_of_conversions {α β : Type*}
    [e : Encoding (List Bool) α] [d : Encoding (List Bool) β]
    [r : Encoding Tree α] [s : Encoding Tree β]
    (hi : _root_.id ∈ @FP Tree α α (bitListEncoding.toEncoding.comp e) r timeSpaceModel)
    (ho : _root_.id ∈ @FP Tree β β s (bitListEncoding.toEncoding.comp d) timeSpaceModel) :
    FP (α := α) (β := β) timeSpaceModel ⊆ FP TM.timeSpaceModel :=
  (fp_subset_stack_of_conversions hi ho).trans StackMachine.fp_subset_tm

/-- Polynomially compatible encodings transport tree polynomial time through stack machines. -/
theorem fp_subset_tm {α β : Type*}
    [Encoding (List Bool) α] [Encoding (List Bool) β]
    [Encoding Tree α] [Encoding Tree β]
    [Encoding.PolytimeCompatible α] [Encoding.PolytimeCompatible β] :
    FP (α := α) (β := β) timeSpaceModel ⊆ FP TM.timeSpaceModel :=
  fp_subset_stack.trans StackMachine.fp_subset_tm

end Complexity.TreeMachine
