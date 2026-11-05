/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.TreeTuringSimulation
import Complexity.Classes.TreeFunctions.Composition
import Complexity.Encoding.Fin
import Complexity.Encoding.Nat

open Complexity

namespace TreeSimulationTest

-- The default simulation needs no per-type encoding compatibility.
example (f : Bool → Bool) (h : f ∈ FP .sizeCostTree) :
    f ∈ FP .stack := TreeMachine.fp_subset_stack h

example (f : Bool → Bool) (h : f ∈ FP .sizeCostTree) : f ∈ FP .tm :=
  TreeMachine.fp_subset_tm h

example : (id : Bool → Bool) ∈ FP .tm :=
  TreeMachine.fp_subset_tm TreeMachine.fp_id

example (f : Fin 3 → Fin 2) (h : f ∈ FP .sizeCostTree) : f ∈ FP .tm :=
  TreeMachine.fp_subset_tm h

-- Nonunique tree interpretations lift without an additional raw encoding instance.
inductive Redundant where | value

instance : Encoding Tree Redundant where
  decode _ := pure .value
  exists_code a := by cases a; exact ⟨.nil, Part.mem_some _⟩

example (h : (id : Redundant → Redundant) ∈ FP .sizeCostTree) :
    (id : Redundant → Redundant) ∈ FP .stack :=
  TreeMachine.fp_subset_stack h

-- `ComputableIn` conversions are methods of the shared specification, with distinct stack
-- sources. Tree space counts the input, so it also bounds the stack machine's loading time.
example {α β : Type*} [Encoding Tree α] [Encoding Tree β]
    {f : α → β} {t s : α → ℕ}
    (h : TimeSpaceModel.sizeCostTree.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.stack.ComputableIn f
      IsO(fun a => t a * s a + s a) IsO(s) :=
  h.toUnitTime.toSizeCost.toStack_of_tree

-- The opposite route retains the real initial-cell space cost on returning to TM.
example {f : Bool → Bool} {t s : Bool → ℕ}
    (h : TimeSpaceModel.tm.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.tm.ComputableIn f IsO(t) IsO(fun a => s a + 1) :=
  h.toStack_of_tm.toTM

end TreeSimulationTest
