/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Basic
public import Complexity.Data.FinEnum

/-! # Evaluating finite tape banks in executable regression tests

The mathematical configuration stores its tape bank as a function. Repeated reads can
recompute earlier updates. Materializing the finite bank after each transition avoids this
host-runtime cost without changing any configuration or the number of machine steps.
-/

@[expose] public section

namespace ComplexityTest.TMRun

open Complexity

variable {κ Γ Q : Type} [FinEnum κ] [Inhabited Γ] {xs : Array Γ}

def materialize (c : TM.Cfg κ Γ xs) : TM.Cfg κ Γ xs :=
  let tapes := Vector.ofFn fun i : Fin (FinEnum.card κ) ↦ c.workTapes (FinEnum.equiv.symm i)
  let heads := Vector.ofFn fun i : Fin (FinEnum.card κ) ↦ c.workPos (FinEnum.equiv.symm i)
  { c with workTapes := fun i ↦ tapes[FinEnum.equiv i]
           workPos := fun i ↦ heads[FinEnum.equiv i] }

@[simp] theorem materialize_eq (c : TM.Cfg κ Γ xs) : materialize c = c := by
  apply TM.Cfg.ext <;> try rfl
  all_goals funext i; simp [materialize]

def step (M : TM Id κ Γ Q) (c : Q × TM.Cfg κ Γ xs) : Q × TM.Cfg κ Γ xs :=
  let d := M.step c
  (d.1, materialize d.2)

@[simp] theorem step_eq (M : TM Id κ Γ Q) (c : Q × TM.Cfg κ Γ xs) : step M c = M.step c := by
  simp [step]

def runFrom (M : TM Id κ Γ Q) : Q × TM.Cfg κ Γ xs → ℕ → Q × TM.Cfg κ Γ xs
  | c, 0 => c
  | c, n + 1 => runFrom M (step M c) n

theorem runFrom_eq (M : TM Id κ Γ Q) (c : Q × TM.Cfg κ Γ xs) (n : ℕ) :
    runFrom M c n = M.runFrom c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [runFrom, step_eq, Controller.runFrom_succ, ih]

end ComplexityTest.TMRun
