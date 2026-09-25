/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Execution
meta import Complexity.Models.TuringMachine.Execution
meta import Complexity.Models.TuringMachine.Cost
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Controller.Cost
meta import Complexity.Control.Controller
meta import Complexity.Control.BinaryChoice
meta import Complexity.Control.Cost
meta import Complexity.Control.Transition.Cost

open Complexity

namespace Complexity.TuringMachineCostTest

-- Visit two fresh blank cells, return to the initial position, and halt.
private def excursion : TM Id Unit Bool (Fin 5) where
  q₀ := 0
  halt q := q == 4
  transition q _ := pure <|
    { inputMove := 0
      work := fun _ => (none, if q.val < 2 then 1 else -1)
      output := none
      state := q + 1 }

private def start : TM.Cfg Unit Bool (Fin 5) #[] :=
  excursion.initInput ([] : List Bool)

private def tracked (n : ℕ) : TM.TrackedCfg Unit Bool (Fin 5) #[] :=
  excursion.run _ ([] : List Bool) n

-- The starting work cell counts even before any action has run.
#guard (tracked 0).space = 1
#guard (tracked 2).space = 3

-- Returning the head over blank data does not forget historical visits.
#guard (tracked 4).cfg.workPos () = 0
#guard (tracked 4).cfg.workSymbols () = false
#guard (tracked 4).visited () = ⟨⟨0, 2⟩, by decide⟩
#guard (tracked 4).space = 3

-- Halting padding changes neither the stored data nor its historical footprint.
#guard (tracked 20).cfg.workPos () = 0
#guard (tracked 20).space = 3
#guard excursion.runConfigMax (Config := TM.TrackedCfg Unit Bool (Fin 5) #[])
  TM.visitedCosts.space ([] : List Bool) 20 = 3
#guard excursion.runActionSum (Config := TM.TrackedCfg Unit Bool (Fin 5) #[])
  TM.visitedCosts.time ([] : List Bool) 20 = 4

-- The correspondence covers every prefix, not only this machine's halting endpoint.
example (n : ℕ) : (tracked n).cfg = excursion.runFrom start n :=
  excursion.tracked_runFrom_cfg start.track n

example (n : ℕ) : excursion.runConfigMaxFrom TM.visitedCosts.space
    start.track n = excursion.spaceUsed start n := rfl

-- Recording can also begin in the middle of a computation, away from head zero.
private def freshResume : TM.TrackedCfg Unit Bool (Fin 5) #[] :=
  let c : TM.Cfg Unit Bool (Fin 5) #[] :=
    { start with state := 2, workPos := fun _ => 7 }
  excursion.runFrom c.track 2

#guard freshResume.cfg.workPos () = 5
#guard freshResume.visited () = ⟨⟨5, 7⟩, by decide⟩
#guard freshResume.space = 3

-- Resume at the left boundary while retaining cells visited earlier on the right.
private def resumeStart : TM.TrackedCfg Unit Bool (Fin 5) #[] where
  cfg := { start with state := 2, workPos := fun _ => -2 }
  visited := fun _ => ⟨⟨-2, 3⟩, by decide⟩
  head_mem := by intro i; change (-2 : ℤ) ≤ -2 ∧ -2 ≤ 3; decide

private def resumed : TM.TrackedCfg Unit Bool (Fin 5) #[] :=
  excursion.runFrom resumeStart 2

#guard resumed.cfg.workPos () = -4
#guard (resumed.visited ()).fst = -4
#guard (resumed.visited ()).snd = 3
#guard resumed.space = 8

-- Peak space also preserves the prior history through halted padding.
#guard excursion.runConfigMaxFrom TM.visitedCosts.space resumeStart 20 = 8

end Complexity.TuringMachineCostTest
