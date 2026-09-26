/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Specification.Tracked

set_option experimental.vcgen true

open Complexity (TM)
open Complexity.TM Std.WP

namespace ProgramConfigurationTest

def once : TM.Program (Fin 0) Bool Unit := Program.repeatUntil (pure true)

-- A named invariant works for both interpretations of the same compiled program.
theorem once_cfg :
    Triple (once.verify (Program.cfgSemantics #[])) (fun _ b ↦ b = 1)
      (fun _ _ b ↦ b = 0) () := by
  unfold once
  vcgen invariants
  | inv1 => fun _ n ↦ n = 1
  all_goals simp_all

theorem once_tracked :
    Triple (once.verify (Program.semantics #[])) (fun _ b ↦ b = 1)
      (fun _ _ b ↦ b = 0) () := by
  unfold once
  vcgen invariants
  | inv1 => fun _ n ↦ n = 1
  all_goals simp_all

def echo : TM.Program (Fin 0) Bool Unit := do
  let a ← Program.readInput
  Program.emit a

-- Registered primitive rules preserve data and exact remaining credits.
theorem echo_spec (xs : Array Bool) (c : Cfg (Fin 0) Bool Unit xs) :
    Triple (echo.verify (Program.cfgSemantics xs)) (fun s b ↦ s = c ∧ b = 2)
      (fun _ s b ↦ s.output = c.output.push c.inputSymbol ∧ b = 0) () := by
  unfold echo
  vcgen
  all_goals simp_all

-- A configuration-only proof still proves a fact about the actual finite controller.
theorem echo_computes (xs : Array Bool) :
    (Program.compile echo).ComputesInTimeAndSpace xs.toList [xs[0]?.getD false] 2 0 := by
  apply Program.cfg_computesInTimeAndSpace (P := fun s b ↦ s = (rawExecution xs.toList).init () ∧ b = 2)
  · constructor
    intro s b hs
    exact (echo_spec xs ((rawExecution xs.toList).init ())).entails_wp_of_post
      (fun _ _ _ h ↦ by simpa [Cfg.inputSymbol] using h.1) s b hs
  · exact ⟨rfl, rfl⟩

end ProgramConfigurationTest
