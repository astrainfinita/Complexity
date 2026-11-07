/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

namespace ComplexityTest.SourceTranslation.AsymptoticTailRecursion

def drain (_ : List Bool) : List Bool := []

-- Neither callback budgets nor a chosen credit coefficient occur in this proof.
@[program] theorem hasProgramIn_drain : HasProgramIn drain hole(⊢ program)
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDrain
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
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
  all_goals intro; decide

theorem drain_fdtisp : drain ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

-- The program is determined by the callbacks; tail-loop space has no stack multiplier.
example : ∃ test t p, programDrain = loopCode test List.programTail (fun v => pure v) ∧
    HasProgramInO (fun xs : List Bool => !xs.isEmpty) test t p := by
  -- The callback's program is read off the loop first, then translated.
  refine ⟨_, ?t, ?p, rfl, ?callback⟩
  case callback => source_fun_prop

end ComplexityTest.SourceTranslation.AsymptoticTailRecursion
