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
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
open ComplexityTest.SourceTranslation.Asymptotics

namespace ComplexityTest.SourceTranslation.AsymptoticReuse

-- Loop callbacks reuse the imported selection without unfolding its evaluator.
theorem hasProgramIn_importedLoop :
    HasProgramIn preciseIdentity hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programImportedLoop
  fill_hole program in
    source_fun_prop using loop (test := fun _ : List Bool => false)
      (next := preciseIdentity) (finish := preciseIdentity)
      (invariant := fun x y => x = y) (measure := fun _ => 0)
      (step := fun _ => 1) (stop := fun _ => 1) (space := fun x => ⌜x⌝ₜ.size)
  case equation => intro; rfl
  case initial => intro; rfl
  case next_state => intros; contradiction
  case decreases => intros; contradiction
  case input_size => exact Dominated.of_le fun z => by rw [z.2]
  all_goals intro; decide

example : ∃ test t p,
    programImportedLoop = loopCode test programPreciseIdentity programPreciseIdentity ∧
      HasProgramInO (fun _ : List Bool => false) test t p := by
  -- The callback's program is read off the loop first, then translated.
  refine ⟨_, ?t, ?p, rfl, ?callback⟩
  case callback => source_fun_prop

-- Repeated calls reuse the imported growth, at every input.
example : HasProgramInO (fun xs => preciseIdentity (preciseIdentity xs)) hole(⊢ program)
    (fun _ => 0 + 0) (fun _ => max 0 0) := by
  fill_hole program in source_fun_prop

-- An imported alias also retains the selected program and its zero growth.
example := (by source_fun_prop : HasProgramInO aliasedIdentity programPreciseIdentity _ _)

-- A call of the alias needs the alias's own selected implementation.
theorem hasProgramIn_aliasedIdentity :
    HasProgramIn aliasedIdentity hole(⊢ program) IsO(fun _ => 0) IsO(fun _ => 0) := by
  abstract_hole program using programAliasedIdentity
  fill_hole program in source_fun_prop

attribute [local program] hasProgramIn_aliasedIdentity in
example : HasProgramInO (fun xs => aliasedIdentity (aliasedIdentity xs)) hole(⊢ program)
    (fun _ => 0 + 0) (fun _ => max 0 0) := by
  fill_hole program in source_fun_prop

open ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drainTwice (xs : List Bool) : List Bool := drain (drain xs)

-- The ordinary model entry recognizes positive powers and reuses the imported loop.
-- Neither model overhead nor the loop's callback construction appears in these goals.
theorem drainTwice_fdtisp :
    drainTwice ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop (disch := dominated [drain])

-- A composition on a finite type keeps the constant growths stated by the selected implementation.
example : HasProgramInO (fun b => !!b) hole(⊢ program) (fun _ => 1 + 1) (fun _ => max 1 1) := by
  fill_hole program in source_fun_prop

end ComplexityTest.SourceTranslation.AsymptoticReuse
