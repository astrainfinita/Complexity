/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Deterministic
import Complexity.Control.Controller.RunHistory
meta import Complexity.Models.TuringMachine.Deterministic
meta import Complexity.Models.TuringMachine.Cost
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Controller.Cost
meta import Complexity.Control.Controller.Basic
meta import Complexity.Control.BinaryChoice.Basic

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

private def history (n : ℕ) := excursion.runHistoryFrom start n

-- The starting work cell counts even before any action has run.
#guard (history 0).space = 1
#guard (history 2).space = 3

-- Returning the head over blank data does not forget historical visits.
#guard (history 4).last.workPos () = 0
#guard (history 4).last.workSymbols () = false
#guard (history 4).visited () = ⟨⟨0, 2⟩, by decide⟩
#guard (history 4).space = 3

-- Halting padding changes neither the stored data nor its historical footprint.
#guard (history 20).last.workPos () = 0
#guard (history 20).space = 3
#guard (excursion.runHistory (TM.Cfg Unit Bool (Fin 5) #[]) ([] : List Bool) 20).space = 3
#guard (history 20).length = 4

-- The endpoint projection covers every prefix, including halted padding.
example (n : ℕ) : (history n).last = excursion.runFrom start n :=
  excursion.last_runHistoryFrom start n

-- Pointwise head bounds give the same interval bound on the actual history.
example {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ] {xs : Array Γ}
    (M : TM Id κ Γ Q) (c : TM.Cfg κ Γ Q xs) (n : ℕ) (V : κ → NonemptyInterval ℤ)
    (hb : ∀ i m, m ≤ n → (M.runFrom c m).workPos i ∈ V i) :
    (M.runHistoryFrom c n).space ≤ ∑ i, ((V i).snd + 1 - (V i).fst).toNat :=
  (M.runHistoryFrom c n).space_le_of_visited_le V
    (fun i ↦ (M.runHistoryFrom_visited_le_iff c n i (V i)).mpr (hb i))

-- Recording can also begin in the middle of a computation, away from head zero.
private def freshResume : Controller.History (TM.Cfg Unit Bool (Fin 5) #[])
    (TM.Action Unit Bool (Fin 5)) :=
  let c : TM.Cfg Unit Bool (Fin 5) #[] :=
    { start with state := 2, workPos := fun _ => 7 }
  excursion.runHistoryFrom c 2

#guard freshResume.last.workPos () = 5
#guard freshResume.visited () = ⟨⟨5, 7⟩, by decide⟩
#guard freshResume.space = 3

-- Resume at the left boundary while retaining cells visited earlier on the right.
private def resumeStart : Controller.History (TM.Cfg Unit Bool (Fin 5) #[])
    (TM.Action Unit Bool (Fin 5)) :=
  (fun h ↦ h.snoc
    { inputMove := 0
      work := fun _ ↦ (none, -1)
      output := none
      state := 2 })^[5]
    (Controller.History.nil { start with state := 2, workPos := fun _ ↦ 3 })

private def resumed := excursion.runFrom resumeStart 2

#guard resumed.last.workPos () = -4
#guard (resumed.visited ()).fst = -4
#guard (resumed.visited ()).snd = 3
#guard resumed.space = 8

-- Peak space also preserves the prior history through halted padding.
#guard (excursion.runFrom resumeStart 20).space = 8

end Complexity.TuringMachineCostTest
