/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice
import Complexity.Control.Controller.Cost
meta import Complexity.Control.Controller.Cost
meta import Complexity.Control.Controller
meta import Complexity.Control.BinaryChoice
meta import Complexity.Control.Controller.RunHistory
meta import Complexity.Control.Controller.History
meta import Complexity.Control.Controller.History.Cost

open Complexity

namespace Complexity.ActionCostTest

def branches : Controller BinaryChoice Unit Bool Bool where
  q₀ := false
  halt := id
  transition _ _ i := i == 1

private instance : Controller.HasState Bool Bool where
  state := id

private instance : Controller.Observe Bool Unit where
  observe _ := ()

private instance : Controller.Apply Bool Bool where
  apply _ _ := true

def branchCost : Bool → Bool → ℕ := fun action _ => if action then 7 else 2

-- Coincident endpoints cannot recover which action was selected or its charge.
#guard branches.stepWith Multiset false = ↑[true, true]
#guard (branches.runHistoryFromWith Multiset false 1).map
  (fun h ↦ (h.last, h.actionSum branchCost)) = ↑[(true, 2), (true, 7)]

-- Each branch retains its actual action count and charge after early halting.
#guard (branches.runHistoryFromWith Multiset false 20).map
  (fun h ↦ (h.last, h.length, h.actionSum branchCost)) = ↑[(true, 1, 2), (true, 1, 7)]
#guard (branches.runHistoryFromWith Multiset true 20).map
  (fun h ↦ (h.last, h.length, h.actionSum branchCost)) = ↑[(true, 0, 0)]

def counter : Controller Id ℕ Unit Bool where
  q₀ := false
  halt := id
  transition _ _ := pure ()

private instance : Controller.HasState ℕ Bool where
  state data := decide (3 ≤ data)

private instance : Controller.Observe ℕ ℕ where
  observe := id

private instance : Controller.Apply ℕ Unit where
  apply _ data := data + 1

def counterCost : Unit → ℕ → ℕ := fun _ data => data + 1

-- Control-state types are inferred without an action or an expected result type.
private def inferredState :=
  Controller.state (3 : ℕ)

example : inferredState = true := rfl

-- Charges use the data before each action, giving 1 + 2 + 3.
#guard ((counter.runHistoryFrom 0 20).last, (counter.runHistoryFrom 0 20).actionSum counterCost) =
  (3, 6)
#guard (counter.runHistoryFrom 0 20).length = 3
#guard (counter.runHistoryFrom 0 0).length = 0
#guard (counter.runHistoryFrom 0 20).configs = [0, 1, 2, 3]
#guard (counter.runHistoryFrom 3 20).actionSum counterCost = 0

-- Reading a measurement does not change the recorded execution.
example (data n : ℕ) : (counter.runHistoryFrom data n).last = counter.runFrom data n :=
  counter.last_runHistoryFrom data n

-- Conditions can be attached to a history without changing its data type.
example (data n : ℕ) (h : Controller.History ℕ Unit)
    (hr : counter.RunConditions data n h) : h.first = data := hr.first_eq

example (data n : ℕ) (h : Controller.History ℕ Unit)
    (hr : counter.RunConditions data n h) : h.length ≤ n := hr.length_le

example (data n : ℕ) (h : Controller.History ℕ Unit)
    (hr : counter.RunConditions data n h) (hn : h.length < n) :
    counter.Halted h.last := hr.stopped.resolve_left (by omega)

example (data n : ℕ) (hn : (counter.runHistoryFrom data n).length < n) :
    counter.Halted (counter.runHistoryFrom data n).last :=
  (counter.runHistoryFrom_spec data n).stopped.resolve_left (by omega)

example (n : ℕ) (h : Controller.History Bool Bool)
    (hh : h ∈ branches.runHistoryFromWith Multiset false n) :
    h.first = false ∧ h.length ≤ n := by
  have hr := branches.runHistoryFromWith_mem_spec false n hh
  exact ⟨hr.first_eq, hr.length_le⟩

def counterSpace (data : ℕ) : ℕ := if data = 1 then 20 else data + 2

-- Zero steps still charge the initial data, and the endpoint is included.
#guard (counter.runHistoryFrom 0 0).configSup counterSpace = 2
#guard (counter.runHistoryFrom 0 1).configSup counterSpace = 20

-- The peak survives after the data becomes smaller and after the controller halts.
#guard (counter.runHistoryFrom 0 3).configSup counterSpace = 20
#guard (counter.runHistoryFrom 0 20).configSup counterSpace = 20
#guard (counter.runHistoryFrom 3 20).configSup counterSpace = 5

-- One history supplies the endpoint, total charge, and an earlier space peak.
#guard
  let h := counter.runHistoryFrom 0 20
  (h.last, h.actionSum counterCost, h.configSup counterSpace) = (3, 6, 20)

end Complexity.ActionCostTest
