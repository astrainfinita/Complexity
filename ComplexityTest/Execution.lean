/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import all Init.Data.List.Scan.Basic
import Complexity.Models.TreeMachine.Deterministic
import Complexity.Models.TuringMachine.Deterministic

open Complexity

namespace Complexity.ExecutionTest

-- Halting hypotheses simplify both shared execution and history statistics.
example {k : ℕ} {Q : Type*} (M : TreeMachine Id k Q) (c : TreeMachine.Cfg k Q)
    (h : M.Halted c) (n : ℕ) :
    M.step c = c ∧ M.runFrom c n = c ∧
      (M.runHistoryFrom c n).actionSum TreeMachine.Action.sizeCost = 0 := by
  simp [h]

-- Each model's complete interface recovers its existing resource relation.
example {k : ℕ} [NeZero k] {Q : Type*} (M : TreeMachine Id k Q)
    (a b : Tree) (t s : ℕ) :
    M.computes (Config := TreeMachine.Cfg k Q)
      (fun h ↦ h.actionSum TreeMachine.Action.sizeCost)
      (fun h ↦ h.configSup TreeMachine.Cfg.mass) a b t s ↔
      M.ComputesInTimeAndSpace a b t s :=
  Iff.rfl

example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.computes (Config := TM.Cfg κ Γ Q xs.toArray)
      Controller.History.length Controller.History.space xs ys t s ↔
      M.ComputesInTimeAndSpace xs ys t s :=
  Iff.rfl

-- The unified computation retains the old fixed-time meaning, including halted padding.
example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesInTimeAndSpace xs ys t s ↔
      M.Halted (M.run (TM.Cfg κ Γ Q xs.toArray) xs t) ∧
      (M.run (TM.Cfg κ Γ Q xs.toArray) xs t).output = ys.toArray ∧
      (M.runHistory (TM.Cfg κ Γ Q xs.toArray) xs t).space ≤ s := by
  refine Controller.computes_unit_iff.trans ?_
  simp only [TM.rawExecution_hasOutput]

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

example : oneAction.computes (Config := Bool × ℕ)
    (fun _ ↦ 0) (fun h ↦ h.configSup Prod.snd) () 1 0 1 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

-- Unit costs permit halted padding, but cannot hide the first active step in a zero budget.
example : oneAction.computes (Config := Bool × ℕ)
    Controller.History.length (fun h ↦ h.configSup Prod.snd) () 1 5 1 :=
  Controller.computes_unit_iff.mpr ⟨rfl, rfl, by decide⟩

example : ¬oneAction.computes (Config := Bool × ℕ)
    Controller.History.length (fun h ↦ h.configSup Prod.snd) () 1 0 1 := by
  intro h
  have hh := (Controller.computes_unit_iff.mp h).1
  contradiction

-- The unit-time equivalence also handles history measurements that decrease.
example : oneAction.computes (Config := Bool × ℕ)
    Controller.History.length (fun h ↦ if h.length = 0 then 1 else 0) () 1 5 0 :=
  Controller.computes_unit_iff.mpr ⟨rfl, rfl, by decide⟩

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
    (TM.Cfg (ULift.{1} Unit) (ULift.{2} Bool) (ULift.{3} Bool)
      (#[] : Array (ULift.{2} Bool)))
    (ULift.{3} Bool) (Output := List (ULift.{2} Bool))
    (input := ([] : List (ULift.{2} Bool))) := inferInstance

end Complexity.ExecutionTest
