/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.MachineGrowth

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.MachineGrowthReuse

-- The imported selection, with its own growth, is reused by ordinary calls.
example := (by source_fun_prop :
  HasProgram (id : List Bool → List Bool) MachineGrowth.programSelected _ _)

def nested (xs : List Bool) := id (id xs)

theorem nested_machine : TimeSpaceModel.tree.ComputableIn nested
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop

-- The selected linear program, not the zero-cost identity, runs inside the nested calls.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableIn nested
        IsO(fun _ => 1) IsO(fun xs => ⌜xs⌝ₜ.size) := by
      model_fun_prop
      all_goals
        simp only [Dominated.add_iff]
        repeat' apply And.intro
      all_goals first
        | exact Dominated.refl _
        | exact Dominated.const _
        | exact Dominated.const_of_pos _ fun _ => Tree.size_pos _
  trivial

end ComplexityTest.SourceTranslation.MachineGrowthReuse
