/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drain (_ : List Bool) : List Bool := []

-- Neither callback budgets nor a chosen credit coefficient occur in this proof.
@[source] def implementationDrain : Implementation drain
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop using loop (test := fun xs : List Bool => !xs.isEmpty)
    (next := List.tail) (finish := id)
    (invariant := fun xs ys : List Bool => ys.length ≤ xs.length ∧ ⌜ys⌝ₜ.size ≤ ⌜xs⌝ₜ.size)
    (measure := List.length) (step := fun _ => 1) (stop := fun _ => 1)
    (space := fun xs => ⌜xs⌝ₜ.size)
  case equation => intro xs; cases xs <;> rfl
  case initial => exact fun _ => ⟨le_rfl, le_rfl⟩
  case next_state =>
    intro xs ys hi _
    cases ys <;> simp_all [encode_list_cons, size_encode_prod]
    omega
  case decreases => intro xs ys _ ht; cases ys <;> simp_all
  case input_size => exact Dominated.of_le fun z => z.2.2
  case check_peak => dominated
  case step_peak => exact Dominated.of_le fun z => z.2.2
  case stop_peak => exact Dominated.of_le fun _ => Nat.zero_le _
  case step_time => exact Dominated.refl _
  case check_time => dominated
  case stop_time => exact Dominated.of_le fun _ => Nat.zero_le _
  case time => dominated
  all_goals intro; decide

theorem drain_ftisp : drain ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- The program is determined by the callbacks; tail-loop space has no stack multiplier.
example : implementationDrain.program =
    loopCode (by source_fun_prop : Implementation (fun xs : List Bool => !xs.isEmpty) _ _).program
      (List.implementationTail (α := Bool)).program
      (Implementation.identity (α := List Bool)).program := by
  rfl

end ComplexityTest.SourceTranslation.AsymptoticTailRecursion
