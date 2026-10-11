/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Arithmetic

def add (x : ℕ × ℕ) := x.1 + x.2

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace add
    (fun n => 2000 * n + 10024) (fun n => k * (100 * n + 1002)) := by
  model_fun_prop

def less (x : ℕ × ℕ) := decide (x.1 < x.2)

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace less
    (fun n => 10000 * n + 20000) (fun n => k * (1000 * n + 2000)) := by
  model_fun_prop

def between (x : ℕ × ℕ × ℕ) := decide (x.2.1 ≤ x.1) && decide (x.1 < x.2.2)

example : ∃ b, Realizes between b := ⟨_, by source_fun_prop⟩

example : ∃ b, Realizes (fun x : ℕ × ℕ => decide (x.1 = x.2)) b := ⟨_, by source_fun_prop⟩
example : ∃ b, Realizes (fun x : ℕ × ℕ => x.1 == x.2) b := ⟨_, by source_fun_prop⟩

def addBelow (x : ℕ × ℕ) := if x.1 < x.2 then x.1 + x.2 else x.1

example : ∃ b, Realizes addBelow b := ⟨_, by source_fun_prop⟩

-- A propositional test retains path-sensitive budgets; the unused reverse costs no time.
example : ∃ b, Realizes (fun x : Bool × List Bool =>
    if x.1 = true then x.2.reverse else x.2) b ∧
      ∀ xs, b.time (false, xs) = b.time (false, []) := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro xs
  simp

-- Boolean operations compose through ordinary source syntax.
example : ∃ b, Realizes (fun x : Bool × Bool × Bool =>
    (x.1 && x.2.1) || (x.2.2 && (x.1 || x.2.1))) b := ⟨_, by source_fun_prop⟩

-- Addition by one retains the existing cheaper implementation and exact budget.
example : ∃ b, Realizes (fun n : ℕ => n + 1) b ∧
    ∀ n, b.time n = 28 * n.bits.length + 25 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

end ComplexityTest.SourceTranslation.Arithmetic
