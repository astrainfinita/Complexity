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
example : TreeProgram.Source.Implementation (List.reverse (α := Bool)) := by
  source_fun_prop using tabulate

-- Imported source equalities and a saved user choice are reused inside ordinary calls.
example : TreeProgram.Source.Implementation
    (fun xs : List Bool => some (Guidance.userReverse xs)) := by source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] : TreeProgram.Source.Implementation
    (fun xs : List α => some (Guidance.chosenReverse xs)) := by source_fun_prop

-- A scoped interpretation is selectable from the importing module.
example {α : Type*} [UniqueEncoding Tree α] :
    TreeProgram.Source.Implementation (List.reverse (α := α)) := by
  source_fun_prop using Guidance.ReverseByCases

namespace ComplexityTest.SourceTranslation.Public

open TreeProgram.Source

-- The ordinary entry needs no coefficient, internal namespace or implementation tree.
example : (List.reverse (α := Bool)) ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    apply Dominated.of_le
    intro x
    simp

-- Nested calls reuse the same reversal specification; only output size is rewritten.
example : (fun xs : List Bool => xs.reverse.reverse) ∈ FTISP .tree
    (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    simp only [pow_one, TreeProgram.Source.size_encode_reverse,
      Dominated.add_iff, Dominated.max_iff]
    exact ⟨Dominated.refl _, Dominated.refl _⟩

-- A symbolic positive power uses the saved specification and the standard power exit.
example (m : ℕ) : (List.reverse (α := Bool)) ∈ FTISP .tree
    (fun n => n ^ (m + 1)) (fun n => n ^ 1) := by
  apply Implementation.HasGrowth.mem_ftisp_pow (hf := Implementation.reverse) ?_ (by decide)
  apply Implementation.hasGrowth_reverse.mono
  · exact Dominated.of_le fun xs => Nat.le_self_pow (by omega) _
  · simpa only [pow_one] using (Dominated.refl (fun xs : List Bool => ⌜xs⌝ₜ.size))

-- Ordinary model automation does not accept an exact machine-certificate goal.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableWithin (id : Bool → Bool)
        (fun _ => 4) (fun b => (encode Tree b).size + 3) := by model_fun_prop
  trivial

end ComplexityTest.SourceTranslation.Public
