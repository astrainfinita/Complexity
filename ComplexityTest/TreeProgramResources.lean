/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Language.Expression

set_option experimental.vcgen true

open Complexity TreeMachine Std.WP
open Controller (History)

namespace Complexity.TreeProgramResourcesTest

-- Copying restores the input, but its temporary pair is larger than both endpoints.
private def copyInput : TreeMachine.Program Id 1 Unit := TreeMachine.Program.copy 0 0 0

private theorem copyInput_unit (x : Tree) :
    copyInput.compile.ComputesWithinUnitTime x x 2 (2 * x.size + 1) := by
  apply TreeMachine.Program.computesWithinUnitTime
    (P := fun h b ↦ h = History.nil ⟨input 0 x⟩ ∧ b = 2) (hp := ⟨rfl, rfl⟩)
  unfold copyInput TreeMachine.Program.copy
  vcgen
  all_goals simp_all [Cfg.mass, Tree.size_pair] <;> omega

-- Size charging uses the same machine and the proved intermediate-space bound.
example (x : Tree) :
    copyInput.compile.ComputesWithin x x (2 * (2 * x.size + 1)) (2 * x.size + 1) :=
  (copyInput_unit x).toSizeCost

-- A program that returns immediately still accounts for the initial input tree.
example (x : Tree) :
    (pure () : TreeMachine.Program Id 1 Unit).compile.ComputesWithinUnitTime x x 0 x.size := by
  apply TreeMachine.Program.computesWithinUnitTime_of_exec
    (Program.Exec.pure TreeMachine.Program.historySemantics () (History.nil ⟨input 0 x⟩))
    le_rfl
  · simp
  · simp [Cfg.mass]

-- Reading a root consumes a unit even though it does not change any register.
example (x : Tree) :
    (TreeMachine.Program.root (0 : Fin 1)).compile.ComputesWithinUnitTime x x 1 x.size := by
  apply TreeMachine.Program.computesWithinUnitTime
    (P := fun h b ↦ h = History.nil ⟨input 0 x⟩ ∧ b = 1) (hp := ⟨rfl, rfl⟩)
  vcgen
  all_goals simp_all [Cfg.mass]

-- A discarded subtree still contributes to the source bound and the compiled peak.
private def projectPair : TreeProgram.Expr Unit := .left (.pair (.var ()) (.var ()))

private def projectPairCode : TreeMachine.Program Id 3 Unit :=
  projectPair.assign 0 (fun _ ↦ 0) 1 2 (by decide)

example (x : Tree) :
    projectPairCode.compile.ComputesWithinUnitTime x x 2 (3 * (2 * x.size + 3)) := by
  obtain ⟨h, hr, hout, hpeak⟩ := projectPair.exec_assign_history (0 : Fin 3) (fun _ ↦ 0) 1 2
    (by decide) (by intro; decide) (by decide)
    (History.nil ⟨input 0 x⟩) (by simp)
  apply TreeMachine.Program.computesWithinUnitTime_of_exec hr (by decide)
  · simpa [projectPair] using hout 0 (by decide)
  · apply (TreeMachine.configSup_mass_le_sum h).trans
    calc
      _ ≤ ∑ _ : Fin 3, (2 * x.size + 3) := Finset.sum_le_sum fun i _ ↦ by
        have hi := hpeak i
        have hx := Tree.size_pos x
        by_cases h0 : i = 0 <;> simp [projectPair, h0, input_get_of_ne, Tree.size_pair] at hi ⊢ <;>
          omega
      _ = _ := by simp

end Complexity.TreeProgramResourcesTest
