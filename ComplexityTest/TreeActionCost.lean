/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import all Init.Data.List.Scan.Basic
import Complexity.Classes.TreeFunctions.UnitTime
import Complexity.Encoding.Tree
import Mathlib.Tactic.NormNum

open Complexity Complexity.TreeMachine

namespace Complexity.TreeActionCostTest

def pairOnce : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (true, .pair 0 0 0)

-- The same program and data incur three size units, or one unit of step time.
example : pairOnce.ComputesWithin Tree.nil (Tree.pair Tree.nil Tree.nil) 3 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

private theorem pairOnce_unit :
    pairOnce.ComputesInUnitTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : pairOnce.ComputesWithin Tree.nil (Tree.pair Tree.nil Tree.nil) 3 3 :=
  pairOnce_unit.toSizeCost

-- Shrinking pays for the source; the unit-to-size bound uses the peak before the write.
def rightOnce : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (true, .right 0 0)

example : rightOnce.ComputesWithin
    (.pair (.pair .nil .nil) .nil) .nil 5 5 := by
  have h : rightOnce.ComputesInUnitTimeAndSpace
      (.pair (.pair .nil .nil) .nil) .nil 1 5 := by
    refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide
  exact h.toSizeCost

-- Padding the requested run does not add to the recorded unit-time cost.
example : pairOnce.ComputesInUnitTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  refine ⟨10, rfl, rfl, ?_, ?_⟩ <;> decide

-- One machine handles every input code, with budgets measured on that code.
private theorem pairBool_unit :
    TimeSpaceModel.tree.ComputableWithin
      (fun b : Bool ↦ Tree.pair (encode Tree b) (encode Tree b))
      (fun _ ↦ 1) (fun b ↦ 2 * (encode Tree b).size + 1) := by
  refine ⟨_, ⟨1, inferInstance, Bool, inferInstance, pairOnce, rfl⟩, ?_⟩
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro b
  cases b <;> refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : TimeSpaceModel.sizeCostTree.ComputableWithin
    (fun b : Bool ↦ Tree.pair (encode Tree b) (encode Tree b))
    (fun b ↦ 2 * (encode Tree b).size + 1) (fun b ↦ 2 * (encode Tree b).size + 1) := by
  simpa using pairBool_unit.toSizeCost

-- This difference affects bounded computations, not just reported diagnostic totals.
example : ¬Controller.ComputesWith pairOnce Tree.nil (Tree.pair Tree.nil Tree.nil)
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass) 1 3 := by
  intro h
  have hbound : pairOnce.ComputesWithin _ _ _ _ := h
  have := hbound.output_size_le_mass_add_time
  norm_num [pairOnce, Cfg.mass, input, Tree.size] at this

-- The execution also uses the selected state-space measure.
example : Controller.ComputesWith pairOnce Tree.nil (Tree.pair Tree.nil Tree.nil)
    Controller.History.length (fun _ ↦ 0) 1 0 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : ¬Controller.ComputesWith pairOnce Tree.nil (Tree.pair Tree.nil Tree.nil)
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass) 3 2 := by
  intro h
  have hbound : pairOnce.ComputesWithin _ _ _ _ := h
  have := hbound.output_size_le_space
  norm_num [Tree.size] at this

end Complexity.TreeActionCostTest
