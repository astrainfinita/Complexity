/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import all Init.Data.List.Scan.Basic
import Complexity.Models.TreeMachine.Deterministic
import Mathlib.Tactic.NormNum

open Complexity Complexity.TreeMachine

namespace Complexity.TreeActionCostTest

def pairOnce : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign true (.pair 0 0 0)

-- The same program and data incur three size units, or one unit of step time.
example : Controller.computes (Config := Cfg 1 Bool) pairOnce
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 3 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : Controller.computes (Config := Cfg 1 Bool) pairOnce
    Controller.History.length (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

-- This difference affects bounded computations, not just reported diagnostic totals.
example : ¬Controller.computes (Config := Cfg 1 Bool) pairOnce
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 1 3 := by
  intro h
  have hbound : pairOnce.ComputesInTimeAndSpace _ _ _ _ := h
  have := hbound.output_size_le_mass_add_time
  norm_num [pairOnce, initInput_tree,  Cfg.mass, input, Tree.size] at this

-- The execution also uses the selected state-space measure.
example : Controller.computes (Config := Cfg 1 Bool) pairOnce
    Controller.History.length (fun _ ↦ 0) Tree.nil (Tree.pair Tree.nil Tree.nil) 1 0 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

example : ¬Controller.computes (Config := Cfg 1 Bool) pairOnce
    (fun h ↦ h.actionSum Action.sizeCost) (fun h ↦ h.configSup Cfg.mass)
    Tree.nil (Tree.pair Tree.nil Tree.nil) 3 2 := by
  intro h
  have hbound : pairOnce.ComputesInTimeAndSpace _ _ _ _ := h
  have := hbound.output_size_le_space
  norm_num [Tree.size] at this

end Complexity.TreeActionCostTest
