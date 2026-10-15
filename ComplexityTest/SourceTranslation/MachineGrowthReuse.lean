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

noncomputable def selected : Implementation (id : List Bool → List Bool) := by source_fun_prop

-- The widened machine exit has not overwritten the original zero-resource source spec.
example : selected.HasGrowth (fun _ => 0) (fun _ => 0) :=
  MachineGrowth.identity_machine.hasGrowth_sourceImplementation

-- Separate saved aliases retain the same program and specification; their private records
-- need not be definitionally equal after import.
example : ∃ hf : Implementation (id : List Bool → List Bool),
    hf.program = selected.program ∧ hf.HasGrowth (fun _ => 0) (fun _ => 0) := by
  refine ⟨_, ?_, MachineGrowth.canonical_machine.hasGrowth_sourceImplementation⟩
  simp only [selected, MachineGrowth.canonical_machine.program_sourceImplementation]

example : (selected.comp selected).HasGrowth (fun _ => 0 + 0) (fun _ => max 0 0) := by
  source_fun_prop
  all_goals exact Dominated.refl _

def nested (xs : List Bool) := id (id xs)

@[source] theorem nested_machine : TimeSpaceModel.tree.ComputableWithGrowth nested
    (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop
  · exact Dominated.const _
  · simp only [Nat.max_zero, Dominated.add_iff]
    exact ⟨Dominated.refl _, Dominated.const_of_pos _ fun _ => Tree.size_pos _⟩

end ComplexityTest.SourceTranslation.MachineGrowthReuse
