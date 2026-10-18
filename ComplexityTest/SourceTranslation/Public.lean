/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import ComplexityTest.SourceTranslation.Guidance

noncomputable section

open Complexity ComplexityTest.SourceTranslation

-- The built-in implementation scope needs no namespace-opening command.
example := (by source_fun_prop using tabulate :
  TreeProgram.Source.Implementation (List.reverse (α := Bool)) _ _)

-- Imported source equalities and a saved user choice are reused inside ordinary calls.
example := (by source_fun_prop : TreeProgram.Source.Implementation
    (fun xs : List Bool => some (Guidance.userReverse xs)) _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  TreeProgram.Source.Implementation (fun xs : List α => some (Guidance.chosenReverse xs)) _ _)

-- A scoped interpretation is selectable from the importing module.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using Guidance.ReverseByCases :
  TreeProgram.Source.Implementation (List.reverse (α := α)) _ _)

namespace ComplexityTest.SourceTranslation.Public

open TreeProgram.Source

-- The ordinary entry needs no coefficient, internal namespace or implementation tree.
example : (List.reverse (α := Bool)) ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- Nested calls reuse the same reversal specification; only output size is rewritten.
example : (fun xs : List Bool => xs.reverse.reverse) ∈ FTISP .tree
    (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

-- A symbolic positive power uses the saved specification and the standard power exit.
example (m : ℕ) : (List.reverse (α := Bool)) ∈ FTISP .tree
    (fun n => n ^ (m + 1)) (fun n => n ^ 1) := by
  apply Implementation.mem_ftisp_pow ?_ (by decide)
  apply Implementation.reverse.mono
  · exact Dominated.of_le fun xs => Nat.le_self_pow (by omega) _
  · simpa only [pow_one] using (Dominated.refl (fun xs : List Bool => ⌜xs⌝ₜ.size))

-- Ordinary model automation does not accept an exact machine-certificate goal.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableWithin (id : Bool → Bool)
        (fun _ => 4) (fun b => (encode Tree b).size + 3) := by model_fun_prop
  trivial

end ComplexityTest.SourceTranslation.Public
