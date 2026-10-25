/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.TailRecursion

@[expose] public section

open Complexity
open ComplexityTest.SourceTranslation.TailRecursion

open TreeProgram.Source

-- Importing restores the selected loop program and its growth.
example : (by source_fun_prop : Implementation keep _ _).program =
    implementationKeep.program := rfl
example : Implementation keep (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by source_fun_prop
example : keep ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

example : True := by
  fail_if_success
    have : Implementation keep (fun _ => 0) (fun _ => 0) := by
      source_fun_prop
      all_goals exact Dominated.zero
  trivial

def optionalGather : Option (Bool × List (List Bool) × List Bool) → List Bool
  | none => []
  | some x => gather x

-- Ordinary nested calls consume gather's linear selected growth.
example : optionalGather ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated
