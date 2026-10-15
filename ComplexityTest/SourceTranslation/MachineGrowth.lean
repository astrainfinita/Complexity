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
@[source] theorem identity_machine : TimeSpaceModel.tree.ComputableWithGrowth
    (id : List Bool → List Bool) (fun xs => xs.length + 1) (fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop
  · exact Dominated.const_of_pos _ fun _ => Nat.succ_pos _
  · simp only [Nat.max_zero, Dominated.add_iff]
    exact ⟨Dominated.refl _, Dominated.const_of_pos _ fun _ => Tree.size_pos _⟩

-- Direct exits also retain the registered specification, even when their proof weakens it.
@[source] theorem canonical_machine : TimeSpaceModel.tree.ComputableWithGrowth
    (id : List Bool → List Bool) (fun _ => 1 + 4)
      (fun xs => max ⌜xs⌝ₜ.size 1 + 2) :=
  (identity_machine.hasGrowth_sourceImplementation.mono
    (Dominated.zero : Dominated (fun _ : List Bool => 0) (fun _ => 1))
    Dominated.zero).computableWithGrowth

-- A chosen implementation is reused even when another program computes the same function.
example (hf : Implementation (id : List Bool → List Bool))
    (hg : hf.HasGrowth (fun _ => 0) (fun _ => 0)) :
    TimeSpaceModel.tree.ComputableWithGrowth (id : List Bool → List Bool)
      (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  model_fun_prop
  · exact Dominated.const _
  · simp only [Nat.max_zero, Dominated.add_iff]
    exact ⟨Dominated.refl _, Dominated.const_of_pos _ fun _ => Tree.size_pos _⟩

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

end ComplexityTest.SourceTranslation.MachineGrowth
