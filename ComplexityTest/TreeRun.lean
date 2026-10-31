/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Mathlib.Data.Vector.Basic

/-! # Evaluating finite tree-register banks in regression tests

As in `TMRun`, materialization prevents repeated evaluation of old functional updates.
The resulting configuration is equal to the original mathematical run at every step.
-/

@[expose] public section

namespace ComplexityTest.TreeRun

open Complexity

variable {k : ℕ} {Q : Type}

def materialize (c : TreeMachine.Cfg k) : TreeMachine.Cfg k :=
  let regs := Vector.ofFn c.regs
  { regs := fun i ↦ regs[i] }

@[simp] theorem materialize_eq (c : TreeMachine.Cfg k) : materialize c = c := by
  apply TreeMachine.Cfg.ext
  funext i; simp [materialize]

def runFrom (M : TreeMachine Id k Q) : Q × TreeMachine.Cfg k → ℕ → Q × TreeMachine.Cfg k
  | c, 0 => c
  | c, n + 1 =>
    let d := M.step c
    runFrom M (d.1, materialize d.2) n

theorem runFrom_eq (M : TreeMachine Id k Q) (c : Q × TreeMachine.Cfg k) (n : ℕ) :
    runFrom M c n = M.runFrom c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [runFrom, materialize_eq, Controller.runFrom_succ, ih]

end ComplexityTest.TreeRun
