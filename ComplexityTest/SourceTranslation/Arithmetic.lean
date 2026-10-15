/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Arithmetic

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Arithmetic

def add (x : ℕ × ℕ) := x.1 + x.2

example : add ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    apply Dominated.of_le
    intro x
    simp

def less (x : ℕ × ℕ) := decide (x.1 < x.2)

example : less ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals
    apply Dominated.of_le
    intro x
    simp

def between (x : ℕ × ℕ × ℕ) := decide (x.2.1 ≤ x.1) && decide (x.1 < x.2.2)

example : Nonempty (Implementation between) := ⟨by source_fun_prop⟩

example : Nonempty (Implementation (fun x : ℕ × ℕ => decide (x.1 = x.2))) := ⟨by source_fun_prop⟩
example : Nonempty (Implementation (fun x : ℕ × ℕ => x.1 == x.2)) := ⟨by source_fun_prop⟩

def addBelow (x : ℕ × ℕ) := if x.1 < x.2 then x.1 + x.2 else x.1

example : Nonempty (Implementation addBelow) := ⟨by source_fun_prop⟩

-- A propositional test retains path-sensitive budgets; the unused reverse costs no time.
example : ∃ impl : Implementation (fun x : Bool × List Bool =>
    if x.1 = true then x.2.reverse else x.2),
      ∀ xs, impl.bounds.time (false, xs) = impl.bounds.time (false, []) := by
  refine ⟨by source_fun_prop, ?_⟩
  intro xs
  simp

-- Boolean operations compose through ordinary source syntax.
example : Nonempty (Implementation (fun x : Bool × Bool × Bool =>
    (x.1 && x.2.1) || (x.2.2 && (x.1 || x.2.1)))) := ⟨by source_fun_prop⟩

-- Addition by one keeps the selected successor program.
example : (show Implementation (fun n : ℕ => n + 1) from by source_fun_prop).program =
    Implementation.succ.program := rfl

end ComplexityTest.SourceTranslation.Arithmetic
