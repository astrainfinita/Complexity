/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.Asymptotics
public import ComplexityTest.SourceTranslation.AsymptoticTailRecursion

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
open ComplexityTest.SourceTranslation.Asymptotics

namespace ComplexityTest.SourceTranslation.AsymptoticReuse

-- Loop callbacks reuse the imported selection without unfolding its evaluator.
def importedLoop :
    Implementation preciseIdentity (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop using loop (test := fun _ : List Bool => false)
    (next := preciseIdentity) (finish := preciseIdentity)
    (invariant := fun x y => x = y) (measure := fun _ => 0)
    (step := fun _ => 1) (stop := fun _ => 1) (space := fun x => ⌜x⌝ₜ.size)
  case equation => intro; rfl
  case initial => intro; rfl
  case next_state => intros; contradiction
  case decreases => intros; contradiction
  case input_size => exact Dominated.of_le fun z => by rw [z.2]
  case check_peak | step_peak | stop_peak | step_time | check_time | stop_time =>
    exact Dominated.zero
  case time => exact Dominated.const _
  all_goals intro; decide

example : importedLoop.program = loopCode (by source_fun_prop :
    Implementation (fun _ : List Bool => false) _ _).program
    preciseIdentityImplementation.program preciseIdentityImplementation.program := rfl

-- Repeated calls reuse the imported growth, at every input.
example : Implementation (fun xs => preciseIdentity (preciseIdentity xs))
    (fun _ => 0 + 0) (fun _ => max 0 0) := by source_fun_prop

-- An imported alias also retains the selected program and its zero growth.
example : (by source_fun_prop : Implementation aliasedIdentity _ _).program =
    preciseIdentityImplementation.program := rfl

example : Implementation (fun xs => aliasedIdentity (aliasedIdentity xs))
    (fun _ => 0 + 0) (fun _ => max 0 0) := by source_fun_prop

open ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drainTwice (xs : List Bool) : List Bool := drain (drain xs)

-- The ordinary model entry recognizes positive powers and reuses the imported loop.
-- Neither model overhead nor the loop's callback construction appears in these goals.
theorem drainTwice_ftisp :
    drainTwice ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- A zero atTop conclusion on a finite type retains the positive selected callback.
example : (by source_fun_prop : Implementation Bool.not _ _).program =
    finiteNotImplementation.program := rfl

example : Implementation (fun b => !!b) (fun _ => 1 + 1) (fun _ => max 1 1) := by
  source_fun_prop

end ComplexityTest.SourceTranslation.AsymptoticReuse
