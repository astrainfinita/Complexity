/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Arithmetic

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Arithmetic

def add (x : ℕ × ℕ) := x.1 + x.2

example : add ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

def less (x : ℕ × ℕ) := decide (x.1 < x.2)

example : less ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

def between (x : ℕ × ℕ × ℕ) := decide (x.2.1 ≤ x.1) && decide (x.1 < x.2.2)

example := (by source_fun_prop : HasProgram between _ _ _)

example := (by source_fun_prop : HasProgram (fun x : ℕ × ℕ => decide (x.1 = x.2)) _ _ _)
example := (by source_fun_prop : HasProgram (fun x : ℕ × ℕ => x.1 == x.2) _ _ _)

def addBelow (x : ℕ × ℕ) := if x.1 < x.2 then x.1 + x.2 else x.1

example := (by source_fun_prop : HasProgram addBelow _ _ _)

-- A propositional test retains path-sensitive growth; the unused reverse is not charged.
example : HasProgram (fun x : Bool × List Bool => if x.1 = true then x.2.reverse else x.2) hole(⊢ program)
    (fun x => if x.1 then ⌜x⌝ₜ.size else 1) (fun x => ⌜x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

-- Boolean operations compose through ordinary source syntax.
example := (by source_fun_prop : HasProgram (fun x : Bool × Bool × Bool =>
    (x.1 && x.2.1) || (x.2.2 && (x.1 || x.2.1))) _ _ _)

-- Addition by one keeps the selected successor program.
example := (by source_fun_prop : HasProgram (fun n : ℕ => n + 1) Nat.Code.succ _ _)

end ComplexityTest.SourceTranslation.Arithmetic
