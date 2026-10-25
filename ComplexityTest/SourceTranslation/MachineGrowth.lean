/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.MachineGrowth

-- The time budget depends on the value, without imposing a size envelope.
theorem identity_machine : TimeSpaceModel.tree.ComputableWithGrowth
    (id : List Bool → List Bool) (fun xs => xs.length + 1) (fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop
  all_goals dominated

-- A local implementation is used by the machine exit.
example (_hf : Implementation (id : List Bool → List Bool) (fun _ => 0) (fun _ => 0)) :
    TimeSpaceModel.tree.ComputableWithGrowth (id : List Bool → List Bool)
      (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop
  all_goals dominated

-- Loading and running still cost time: a zero machine allowance cannot replace the program.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableWithGrowth (id : List Bool → List Bool)
        (fun _ => 0) (fun xs => ⌜xs⌝ₜ.size) := by
      model_fun_prop
      all_goals exact Dominated.zero
  trivial

-- The all-input machine budget does not become vacuous on finite input types.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableWithGrowth (id : Unit → Unit)
        (fun _ => 0) (fun _ => 0) := by
      model_fun_prop
      all_goals exact Dominated.zero
  trivial

/-- A deliberately slower program for the identity, saved as the selected implementation. -/
@[source] def implementationSelected : Implementation (id : List Bool → List Bool) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) :=
  ((List.implementationReverse.comp List.implementationReverse).congr (by funext xs; simp)).mono
    (Dominated.of_le_mul 2 fun _ => by simp; omega) (Dominated.of_le fun _ => by simp)

-- Direct exits keep the stated growth of the selected implementation.
theorem canonical_machine : TimeSpaceModel.tree.ComputableWithGrowth
    (id : List Bool → List Bool) (fun xs => ⌜xs⌝ₜ.size + 4)
      (fun xs => max ⌜xs⌝ₜ.size ⌜xs⌝ₜ.size + 2) :=
  implementationSelected.computableWithGrowth

example : (by source_fun_prop : Implementation (id : List Bool → List Bool) _ _).program =
    implementationSelected.program := rfl

end ComplexityTest.SourceTranslation.MachineGrowth
