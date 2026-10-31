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

namespace Complexity.ComputationTest

-- Halting hypotheses simplify both shared execution and history statistics.
example {k : ℕ} {Q : Type*} (M : TreeMachine Id k Q) (c : Q × TreeMachine.Cfg k)
    (h : M.Halted c) (n : ℕ) :
    M.step c = c ∧ M.runFrom c n = c ∧
      (M.runHistoryFrom c n).snd.actionSum TreeMachine.Action.sizeCost = 0 := by
  simp [h]

-- Each model's complete interface recovers its existing resource relation.
example {k : ℕ} [NeZero k] {Q : Type*} (M : TreeMachine Id k Q)
    (a b : Tree) (t s : ℕ) :
    M.ComputesWith a b (fun h ↦ h.snd.actionSum TreeMachine.Action.sizeCost)
      (fun h ↦ h.snd.configSup TreeMachine.Cfg.mass) t s ↔
      M.ComputesWithin a b t s :=
  Iff.rfl

example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesWith xs ys Controller.History.length (fun h ↦ h.snd.space) t s ↔
      M.ComputesWithin xs ys t s :=
  Iff.rfl

-- The unified computation retains the old fixed-time meaning, including halted padding.
example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesWithin xs ys t s ↔
      M.Halted (M.run xs t) ∧
      (M.run xs t).2.output = ys.toArray ∧
      (M.runHistory xs t).snd.space ≤ s := by
  refine Controller.computesWith_unit_iff.trans ?_
  simp only [TM.hasOutput_isOutput]

-- Zero action fees require an execution length separate from the time budget.
private def oneAction : Controller Id Unit Unit Bool where
  q₀ := false
  halt := id
  transition _ _ := pure (true, ())

private instance : Controller.Observe ℕ Unit where
  observe _ := ()

private instance : Controller.Apply ℕ Unit where
  apply _ n := n + 1

private instance : Controller.HasConfig Unit Unit (fun _ ↦ ℕ) where
  init _ := 0

private instance : Controller.HasOutput ℕ ℕ where
  IsOutput c n := c = n

example : oneAction.ComputesWith () 1 (fun _ ↦ 0) (fun h ↦ h.snd.configSup id) 0 1 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

-- Unit costs permit halted padding, but cannot hide the first active step in a zero budget.
example : oneAction.ComputesWith () 1
    Controller.History.length (fun h ↦ h.snd.configSup id) 5 1 :=
  Controller.computesWith_unit_iff.mpr ⟨rfl, rfl, by decide⟩

example : ¬oneAction.ComputesWith () 1
    Controller.History.length (fun h ↦ h.snd.configSup id) 0 1 := by
  intro h
  have hh := (Controller.computesWith_unit_iff.mp h).1
  contradiction

-- The unit-time equivalence also handles history measurements that decrease.
example : oneAction.ComputesWith () 1
    Controller.History.length (fun h ↦ if h.length = 0 then 1 else 0) 5 0 :=
  Controller.computesWith_unit_iff.mpr ⟨rfl, rfl, by decide⟩

-- The standard output type is inferred from the output instance.
example : Controller.HasOutput.IsOutput (1 : ℕ) 1 := rfl

-- Configuration capabilities support independent universes and can be supplied separately.
example : Controller.HasState (ULift.{1} Unit) Unit where
  state _ := ()

example : Controller.Observe (ULift.{1} Unit) Unit where
  observe _ := ()

example : Controller.Apply (ULift.{1} Unit) Unit where
  apply _ config := config

example : Controller.Apply Unit (ULift.{1} Unit) where
  apply _ config := config

example : Controller.HasConfig (TreeMachine.Action 1) Tree (fun _ ↦ TreeMachine.Cfg 1) :=
  inferInstance

example : Controller.HasOutput (TreeMachine.Cfg 1) Tree :=
  inferInstance

example (M : TreeMachine Id 1 (ULift.{1} Bool)) : ULift.{1} Bool × TreeMachine.Cfg 1 :=
  M.init Tree.nil

example : Controller.HasConfig (TM.Action (ULift.{1} Unit) (ULift.{2} Bool))
    (List (ULift.{2} Bool)) (fun xs ↦ TM.Cfg (ULift.{1} Unit) (ULift.{2} Bool) xs.toArray) :=
  inferInstance

example : Controller.HasOutput
    (TM.Cfg (ULift.{1} Unit) (ULift.{2} Bool) (#[] : Array (ULift.{2} Bool)))
    (List (ULift.{2} Bool)) := inferInstance

example (M : TM Id (ULift.{1} Unit) (ULift.{2} Bool) (ULift.{3} Bool)) :
    ULift.{3} Bool × TM.Cfg (ULift.{1} Unit) (ULift.{2} Bool) (#[] : Array (ULift.{2} Bool)) :=
  M.init ([] : List (ULift.{2} Bool))

end Complexity.ComputationTest
