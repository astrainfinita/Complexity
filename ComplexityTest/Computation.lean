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

universe u

namespace Complexity.ComputationTest

-- Halting hypotheses simplify both shared execution and history statistics.
example {k : ℕ} {Q : Type*} (M : TreeMachine Id k Q) (c : Q × TreeMachine.Cfg k)
    (h : M.Halted c) (n : ℕ) :
    M.step c = c ∧ M.runFrom c n = c ∧
      (M.runHistoryFrom c n).snd.actionSum TreeMachine.Action.sizeCost = 0 := by
  simp [h]

-- Each model's complete interface recovers its existing resource relation.
example {k : ℕ} [NeZero k] {Q : Type} (M : TreeMachine Id k Q)
    (a b : Tree) (t s : ℕ) :
    M.ComputesWithinCost a b (fun h ↦ h.actionSum TreeMachine.Action.sizeCost)
      (fun h ↦ h.configSup TreeMachine.Cfg.mass) t s ↔
      M.ComputesWithin a b t s :=
  Iff.rfl

example {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesWithinCost xs ys Controller.History.length Controller.History.space t s ↔
      M.ComputesWithin xs ys t s :=
  Iff.rfl

-- The unified computation retains the old fixed-time meaning, including halted padding. Space
-- grows along the run, so its bound at the time budget bounds every depth.
example {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.ComputesWithin xs ys t s ↔
      M.Halted (M.run xs t) ∧
      (M.run xs t).2.output = ys.toArray ∧
      (M.runHistory xs t).snd.space ≤ s := by
  refine Controller.computesWithinCost_unit_iff.trans ?_
  simp only [TM.hasOutput_isOutput]
  refine and_congr_right fun hh ↦ and_congr_right fun _ ↦ ⟨fun hs ↦ hs t, fun hs k ↦ ?_⟩
  rcases le_total k t with hk | hk
  · exact (M.runHistoryFrom_space_mono _ hk).trans hs
  · rwa [M.runHistory_eq_of_halted xs hh hk]

-- Guards that the deterministic `ComputesWithin` is the general `ComputesWithinCostWith` on `Id` by
-- definition.
example {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ] (M : TM Id κ Γ Q) (xs ys : List Γ)
    (t s : ℕ) :
    M.ComputesWithin xs ys t s ↔
      M.ComputesWithinCostWith Id xs (pure ys) Controller.History.length
        Controller.History.space t s :=
  Iff.rfl

-- The two entries of the unified definition work through a model's specification, in the order
-- step, halted, output, time, space. Also records that the definition is not built by an anonymous
-- constructor, since it unfolds to the two clauses of `ComputesWithinCostWith`; if that starts to
-- succeed, the definition can be opened by hand again and the entries are no longer the only way
-- in.
example {κ Γ Q : Type u} [Inhabited Γ] [Fintype κ] (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ)
    (h : M.ComputesWithin xs ys t s) : M.ComputesWithin xs ys t s := by
  obtain ⟨n, hh, ho, ht, hs⟩ := h.exists_halted
  fail_if_success exact ⟨n, hh, ho, ht, hs⟩
  exact .of_halted n hh ho ht hs

-- Records the current universe limitation of the specifications: tape indices, alphabet and
-- control states share one universe, so control states in `Type 1` over `Bool` do not fit. If
-- this starts to succeed, the limitation is gone.
example : True := by
  fail_if_success
    have : ∀ (Q : Type 1) (M : TM Id (Fin 2) Bool Q) (xs ys : List Bool) (t s : ℕ), Prop :=
      fun _ M xs ys t s ↦ M.ComputesWithin xs ys t s
  trivial

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

example : oneAction.ComputesWithinCost () 1 (fun _ ↦ 0) (fun h ↦ h.configSup id) 0 1 :=
  Controller.ComputesWithinCost.of_halted monotone_const
    (fun _ _ ↦ oneAction.configSup_runHistory_mono () id) 1 rfl rfl le_rfl (by decide)

-- Unit costs permit halted padding, but cannot hide the first active step in a zero budget.
example : oneAction.ComputesWithinCost () 1
    Controller.History.length (fun h ↦ h.configSup id) 5 1 :=
  Controller.ComputesWithinCost.of_halted (fun _ _ ↦ oneAction.length_runHistory_mono ())
    (fun _ _ ↦ oneAction.configSup_runHistory_mono () id) 5 rfl rfl (by decide) (by decide)

example : ¬oneAction.ComputesWithinCost () 1
    Controller.History.length (fun h ↦ h.configSup id) 0 1 := by
  intro h
  have hh := (Controller.computesWithinCost_unit_iff.mp h).1
  contradiction

-- Records that the budgets bound the history at every depth, also for a measurement that
-- decreases along the run: this one is `1` on the empty history and `0` afterwards, so a space
-- budget of `0` fails although the halting history measures `0`.
example : ¬oneAction.ComputesWithinCost () 1
    Controller.History.length (fun h ↦ if h.length = 0 then 1 else 0) 5 0 :=
  fun h ↦ absurd (Controller.computesWithinCost_space_le h 0) (by decide)

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
