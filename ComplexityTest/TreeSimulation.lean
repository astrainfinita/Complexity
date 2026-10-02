/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.TreeSimulation
import Complexity.Encoding.Polynomial.Bool

open Complexity

namespace TreeSimulationTest

-- Bool's direct tree code differs from its singleton-list tree code.
example : Encoding.PolytimeCompatible Bool := inferInstance

example (f : Bool → Bool) (h : f ∈ FP TreeMachine.timeSpaceModel) : f ∈ FP TM.timeSpaceModel :=
  TreeMachine.fp_subset_tm h

example : (id : Bool → Bool) ∈ FP TM.timeSpaceModel :=
  TreeMachine.fp_subset_tm TreeMachine.fp_id

-- All bit strings denote the same value: conversion must not assume unique codes.
@[instance_reducible] private def redundant : Encoding (List Bool) Unit where
  decode _ := Part.some ()
  exists_code _ := ⟨[], Part.mem_some ()⟩

local instance : Encoding (List Bool) Unit := redundant
local instance : Encoding Tree Unit := bitListEncoding.toEncoding.comp redundant

example (xs : List Bool) : () ∈ decode Unit (Tree.encodeBitList xs) :=
  (Encoding.mem_comp_encode bitListEncoding redundant).2 (Part.mem_some ())

example : Encoding.PolytimeCompatible Unit := by
  fail_if_success exact inferInstance
  exact Encoding.PolytimeCompatible.ofComp redundant

example : (id : Unit → Unit) ∈ FP TM.timeSpaceModel := by
  let : Encoding.PolytimeCompatible Unit := Encoding.PolytimeCompatible.ofComp redundant
  exact TreeMachine.fp_subset_tm TreeMachine.fp_id

end TreeSimulationTest
