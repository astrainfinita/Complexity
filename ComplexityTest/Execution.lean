/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Deterministic
import Complexity.Models.TuringMachine.Simulation

open Complexity

namespace Complexity.ExecutionTest

-- Halting hypotheses simplify both shared execution and model-specific costs.
example {k : ℕ} {Q : Type*} (M : TreeMachine Id k Q) (c : TreeMachine.Cfg k Q)
    (h : M.Halted c) (n : ℕ) : M.step c = c ∧ M.runFrom c n = c ∧ M.cost c n = 0 := by
  simp [h]

-- Each model's complete interface recovers its existing resource relation.
example {k : ℕ} [NeZero k] {Q : Type*} (M : TreeMachine Id k Q)
    (a b : Tree) (t s : ℕ) :
    Controller.computes (Config := TreeMachine.Cfg k Q) M
      TreeMachine.treeCosts a b t s ↔
      M.ComputesInTimeAndSpace a b t s :=
  Iff.rfl

example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    Controller.computes (Config := TM.TrackedCfg κ Γ Q xs.toArray)
      M TM.visitedCosts xs ys t s ↔
      M.ComputesInTimeAndSpace xs ys t s :=
  Iff.rfl

-- The unified computation retains the old fixed-time meaning, including halted padding.
example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesInTimeAndSpace xs ys t s ↔
      M.Halted (M.run (TM.Cfg κ Γ Q xs.toArray) xs t) ∧
      (M.run (TM.Cfg κ Γ Q xs.toArray) xs t).output = ys.toArray ∧
      M.runConfigMax (Config := TM.TrackedCfg κ Γ Q xs.toArray)
        TM.TrackedCfg.space xs t ≤ s := by
  refine (Controller.computes_unit_iff TM.visitedCosts_time).trans ?_
  simp only [TM.visitedCosts_space, TM.TrackedCfg.hasOutput_def,
    TM.tracked_halted_iff, TM.tracked_run_cfg]

-- Block bounds still measure fresh visits and retain ordinary configuration endpoints.
example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ] {xs : Array Γ}
    (M : TM Id κ Γ Q) (c d : TM.Cfg κ Γ Q xs) (t s : ℕ) :
    M.ReachesInTimeAndSpace c d t s ↔
      ∃ n ≤ t, M.runFrom c n = d ∧
        M.runConfigMaxFrom TM.TrackedCfg.space c.track n ≤ s := by
  simp only [TM.ReachesInTimeAndSpace, TM.tracked_runFrom_cfg, TM.Cfg.track_cfg]

-- Zero action fees require an execution length separate from the time budget.
private def oneAction : Controller Id Unit Unit Bool where
  q₀ := false
  halt := id
  transition _ _ := pure ()

private instance : Controller.HasState (Bool × ℕ) Bool where
  state := Prod.fst

private instance : Controller.Observe (Bool × ℕ) Unit where
  observe _ := ()

private instance : Controller.Apply (Bool × ℕ) Unit where
  apply _ cfg := (true, cfg.2 + 1)

private instance : Controller.Execution (Bool × ℕ) Bool
    (Output := ℕ) (input := ()) where
  init q := (q, 0)
  state_init _ := rfl
  hasOutput cfg n := cfg.2 = n

example : Controller.computes (Config := Bool × ℕ)
    oneAction ⟨fun _ _ => 0, Prod.snd⟩ () 1 0 1 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

-- Unit costs permit halted padding, but cannot hide the first active step in a zero budget.
example (time : Unit → Bool × ℕ → ℕ) (htime : ∀ a c, time a c = 1) :
    oneAction.computes ⟨time, Prod.snd⟩ () 1 5 1 :=
  (Controller.computes_unit_iff htime).mpr ⟨rfl, rfl, by dsimp only; decide⟩

example : ¬oneAction.computes (Config := Bool × ℕ) ⟨(fun _ _ ↦ 1), Prod.snd⟩ () 1 0 1 := by
  intro h
  have hh := ((Controller.computes_unit_iff (fun _ _ ↦ rfl)).mp h).1
  contradiction

-- The standard output type is inferred from the execution instance.
example : Controller.Execution.hasOutput (Config := Bool × ℕ)
    (input := ()) (false, 1) 1 := rfl

-- Configuration capabilities support independent universes and can be supplied separately.
example : Controller.HasState (ULift.{1} Unit) Unit where
  state _ := ()

example : Controller.Observe (ULift.{1} Unit) Unit where
  observe _ := ()

example : Controller.Apply (ULift.{1} Unit) Unit where
  apply _ config := config

example : Controller.Apply Unit (ULift.{1} Unit) where
  apply _ config := config

example : Controller.Execution (TreeMachine.Cfg 1 (ULift.{1} Bool)) (ULift.{1} Bool)
    (Output := Tree) (input := Tree.nil) := inferInstance

example : Controller.Execution
    (TM.TrackedCfg (ULift.{1} Unit) (ULift.{2} Bool) (ULift.{3} Bool)
      (#[] : Array (ULift.{2} Bool)))
    (ULift.{3} Bool) (Output := List (ULift.{2} Bool))
    (input := ([] : List (ULift.{2} Bool))) := inferInstance

end Complexity.ExecutionTest
