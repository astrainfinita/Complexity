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
  all_goals dominated

def less (x : ℕ × ℕ) := decide (x.1 < x.2)

example : less ∈ FTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop
  all_goals dominated

def between (x : ℕ × ℕ × ℕ) := decide (x.2.1 ≤ x.1) && decide (x.1 < x.2.2)

example := (by source_fun_prop : Implementation between _ _)

example := (by source_fun_prop : Implementation (fun x : ℕ × ℕ => decide (x.1 = x.2)) _ _)
example := (by source_fun_prop : Implementation (fun x : ℕ × ℕ => x.1 == x.2) _ _)

def addBelow (x : ℕ × ℕ) := if x.1 < x.2 then x.1 + x.2 else x.1

example := (by source_fun_prop : Implementation addBelow _ _)

-- A propositional test retains path-sensitive growth; the unused reverse is not charged.
example : Implementation (fun x : Bool × List Bool => if x.1 = true then x.2.reverse else x.2)
    (fun x => if x.1 then ⌜x⌝ₜ.size else 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

-- Boolean operations compose through ordinary source syntax.
example := (by source_fun_prop : Implementation (fun x : Bool × Bool × Bool =>
    (x.1 && x.2.1) || (x.2.2 && (x.1 || x.2.1))) _ _)

-- Addition by one keeps the selected successor program.
example : (by source_fun_prop : Implementation (fun n : ℕ => n + 1) _ _).program =
    Implementation.succ.program := rfl

end ComplexityTest.SourceTranslation.Arithmetic
