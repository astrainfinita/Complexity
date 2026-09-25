/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice
import Complexity.Control.Controller.Cost
import Complexity.Control.Cost
meta import Complexity.Control.Controller.Cost
meta import Complexity.Control.Controller
meta import Complexity.Control.Cost
meta import Complexity.Control.BinaryChoice
meta import Complexity.Control.Transition.Cost

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
#guard branches.stepWithCost Multiset branchCost false =
  ↑[(true, 2), (true, 7)]

-- Each branch retains its own charge, even after many halting padding steps.
#guard branches.runFromWithCost Multiset branchCost false 20 =
  ↑[(true, 2), (true, 7)]
#guard branches.runFromWithCost Multiset branchCost true 20 = ↑[(true, 0)]

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
#guard (counter.runFromWithCost Id counterCost 0 20).run =
  (3, 6)
#guard counter.runActionSumFrom counterCost 0 20 = 6
#guard counter.runActionSumFrom (fun _ _ => 1) 0 20 = 3
#guard counter.runActionSumFrom counterCost 3 20 = 0

-- Replacing the cost model preserves execution, including every intermediate endpoint.
example (data n : ℕ) :
    ((counter.runFromWithCost Id counterCost data n).run).fst =
    counter.runFrom data n :=
  congrArg Id.run (counter.fst_runFromWithCost Id counterCost data n)

-- The deterministic accumulator agrees with the branch-aware runner on all prefixes.
example (data n : ℕ) :
    ((counter.runFromWithCost Id counterCost data n).run).snd =
    counter.runActionSumFrom counterCost data n :=
  counter.snd_runFromWithCost counterCost data n

def counterModel : CostModel Unit ℕ where
  time := counterCost
  space data := if data = 1 then 20 else data + 2

-- Zero steps still charge the initial data, and the endpoint is included.
#guard counter.runConfigMaxFrom counterModel.space 0 0 = 2
#guard counter.runConfigMaxFrom counterModel.space 0 1 = 20

-- The peak survives after the data becomes smaller and after the controller halts.
#guard counter.runConfigMaxFrom counterModel.space 0 3 = 20
#guard counter.runConfigMaxFrom counterModel.space 0 20 = 20
#guard counter.runConfigMaxFrom counterModel.space 3 20 = 5

-- Time and space are independent local measurements of the same execution.
#guard counter.runActionSumFrom counterModel.time 0 20 = 6

end Complexity.ActionCostTest
