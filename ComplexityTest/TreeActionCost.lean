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
  transition _ _ := pure <| Action.assign true (.pair 0 0 0)

-- The same program and data incur three size units, or one unit of step time.
example : pairOnce.ComputesInTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 3 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

private theorem pairOnce_unit :
    pairOnce.ComputesInUnitTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : pairOnce.ComputesInTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 3 3 :=
  pairOnce_unit.toSizeCost

-- Padding the requested run does not add to the recorded unit-time cost.
example : pairOnce.ComputesInUnitTimeAndSpace Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  refine ⟨10, rfl, rfl, ?_, ?_⟩ <;> decide

-- One machine handles every input code, with budgets measured on that code.
private theorem pairBool_unit :
    TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun b : Bool ↦ Tree.pair (encode Tree b) (encode Tree b))
      (fun _ ↦ 1) (fun n ↦ 2 * n + 1) := by
  refine ⟨_, ⟨1, inferInstance, Bool, inferInstance, pairOnce, rfl⟩, ?_⟩
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro b
  cases b <;> refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : TimeSpaceModel.sizeCostTree.ComputableInTimeAndSpace
    (fun b : Bool ↦ Tree.pair (encode Tree b) (encode Tree b))
    (fun n ↦ 2 * n + 1) (fun n ↦ 2 * n + 1) := by
  simpa using computableInTimeAndSpace_toSizeCost pairBool_unit

-- This difference affects bounded computations, not just reported diagnostic totals.
example : ¬Controller.ComputesWith (Config := Cfg 1 Bool) pairOnce
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  intro h
  have hbound : pairOnce.ComputesInTimeAndSpace _ _ _ _ := h
  have := hbound.output_size_le_mass_add_time
  norm_num [pairOnce, initInput_tree,  Cfg.mass, input, Tree.size] at this

-- The execution also uses the selected state-space measure.
example : Controller.ComputesWith (Config := Cfg 1 Bool) pairOnce
    Controller.History.length (fun _ ↦ 0) Tree.nil (Tree.pair Tree.nil Tree.nil) 1 0 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : ¬Controller.ComputesWith (Config := Cfg 1 Bool) pairOnce
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 3 2 := by
  intro h
  have hbound : pairOnce.ComputesInTimeAndSpace _ _ _ _ := h
  have := hbound.output_size_le_space
  norm_num [Tree.size] at this

end Complexity.TreeActionCostTest
