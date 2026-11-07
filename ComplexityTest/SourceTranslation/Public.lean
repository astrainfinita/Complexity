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
  TreeProgram.Source.Internal.HasProgram (List.reverse (α := Bool)) _ _ _)

-- Imported source equalities and a saved user choice are reused inside ordinary calls.
example := (by source_fun_prop : TreeProgram.Source.Internal.HasProgram
    (fun xs : List Bool => some (Guidance.userReverse xs)) _ _ _)

example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop :
  TreeProgram.Source.Internal.HasProgram (fun xs : List α => some (Guidance.chosenReverse xs))
    _ _ _)

-- A scoped interpretation is selectable from the importing module.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop using Guidance.ReverseByCases :
  TreeProgram.Source.Internal.HasProgram (List.reverse (α := α)) _ _ _)

namespace ComplexityTest.SourceTranslation.Public

open TreeProgram.Source
open TreeProgram.Source.Internal (HasProgram)

-- The ordinary entry needs no coefficient, internal namespace or implementation tree.
example : List.reverse (α := Bool) ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

-- Nested calls reuse the same reversal specification; only output size is rewritten.
example : (fun xs : List Bool => xs.reverse.reverse) ∈ FDTISP .tree
    (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

-- A symbolic positive power uses the saved specification and the standard power exit.
example (m : ℕ) : List.reverse (α := Bool) ∈ FDTISP .tree
    (fun n => n ^ (m + 1)) (fun n => n ^ 1) := by
  refine HasProgramIn.mem_fdtisp_pow
    (List.hasProgramIn_reverse.mono (fun _ h => h.trans ?_) (fun _ h => h.trans ?_)) (by decide)
  · exact Dominated.of_le fun xs => Nat.le_self_pow (by omega) _
  · simpa only [pow_one] using Dominated.refl (fun xs : List Bool => ⌜xs⌝ₜ.size)

-- Named placeholders in a `refine` take the produced program and growth.
example : ∃ program t p, HasProgram (fun xs : List Bool => xs.reverse.reverse) program t p := by
  refine ⟨?program, ?t, ?p, (?pair : HasProgram _ ?program ?t ?p)⟩
  case pair => source_fun_prop

-- A hole is filled only by `fill_hole`.
/--
error: source translation: the program is the hole `program`; write `fill_hole program in` before the tactic
---
error: (kernel) declaration has metavariables 'ComplexityTest.SourceTranslation.Public._example'
-/
#guard_msgs in
example : HasProgram (List.reverse (α := Bool)) hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size)
    (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop

-- Ordinary model automation does not accept an exact machine-certificate goal.
example : True := by
  fail_if_success
    have : TimeSpaceModel.tree.ComputableWithin (id : Bool → Bool)
        (fun _ => 4) (fun b => (encode Tree b).size + 3) := by model_fun_prop
  trivial

end ComplexityTest.SourceTranslation.Public
