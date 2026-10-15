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

-- Importing the saved model restores its selected program and canonical specification.
noncomputable def recalledKeep : Implementation keep := by source_fun_prop
example : recalledKeep.program = keepImplementation.program := by
  simpa only [recalledKeep] using keep_loop_model.program_sourceImplementation
example : recalledKeep.HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals exact Dominated.refl _
example : keep ∈ FTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals simpa only [pow_zero, pow_one] using Dominated.refl _

example : True := by
  fail_if_success
    have : recalledKeep.HasGrowth (fun _ => 0) (fun _ => 0) := by source_fun_prop
  trivial

def optionalGather : Option (Bool × List (List Bool) × List Bool) → List Bool
  | none => []
  | some x => gather x

-- Ordinary nested calls consume gather's linear saved specification.
example : optionalGather ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    apply Dominated.of_cover (fun _ : Unit => none) some
      (by intro x; cases x with
          | none => exact Or.inl ⟨(), rfl⟩
          | some x => exact Or.inr ⟨x, rfl⟩)
  all_goals
    simp only [Function.comp_def, pow_one, encode_option_none, encode_option_some,
      size_encode_prod, size_encode_unit, encode_list_nil, Dominated.add_iff, Dominated.max_iff]
  all_goals repeat' apply And.intro
  all_goals first
    | exact Dominated.const _
    | exact Dominated.const_of_pos _ (fun _ => by positivity)
    | exact gather_model.hasGrowth_sourceImplementation.1.mono (fun _ => by omega)
    | exact gather_model.hasGrowth_sourceImplementation.2.mono (fun _ => by omega)
    | exact Dominated.of_le (fun _ => by omega)
