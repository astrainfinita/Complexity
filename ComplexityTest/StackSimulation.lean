/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.StackMachine.FromTuringMachine
meta import Complexity.Models.StackMachine.FromTuringMachine
meta import Complexity.Models.StackMachine.Basic
meta import Complexity.Models.StackMachine.Configuration
meta import Complexity.Models.StackMachine.Deterministic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Control.Controller.Basic
meta import Complexity.Control.BinaryChoice.Basic
meta import Mathlib.Data.Fintype.Prod

open Complexity

namespace Complexity.StackSimulationTest

-- Cross both blank frontiers, overwrite true/false/blank, and read each overwritten cell.
private def excursion : TM Id Unit (Option Bool) (Fin 13) where
  q₀ := 0
  halt q := q == 12
  transition q v := pure <|
    { inputMove := if q.val < 2 then -1 else if q.val < 6 then 1 else -1
      work := fun _ ↦ match q.val with
        | 0 | 3 => (none, -1)
        | 1 => (some (some true), 1)
        | 2 => (some (some false), 0)
        | 4 => (some none, -1)
        | 5 | 6 | 10 | 11 => (none, 1)
        | 7 => (some (some true), 0)
        | 8 => (some none, 1)
        | 9 => (some (some false), -1)
        | _ => (none, 0)
      output := some (if q == 0 then v.1 else v.2 ())
      state := q + 1 }

private def source (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) :=
  M.run (TM.Cfg Unit (Option Bool) (Fin 13) (xs.map some).toArray) (xs.map some) n

private def target (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) :=
  M.toStack.run (StackMachine.Cfg (Unit × Bool × Bool) Bool _ xs.toArray) xs n

private def agrees (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) : Bool :=
  let c := source M xs n
  let d := target M xs n
  (c.state.val, c.inputPos.val, c.workSymbols (), c.output.toList.filterMap id) ==
    (d.state.1.val, d.inputPos.val, d.state.2 (), d.output.toList)

-- Compare the actual bounded runs, including every intermediate state and halted padding.
#guard (List.range 16).all (agrees excursion [true, false])
#guard (List.range 16).all (agrees excursion [])
#guard (source excursion [true, false] 12).workPos () = 2
#guard (target excursion [true, false] 12).output = #[true, false, true, false, true, false]
#guard (List.range 16).all fun n ↦ (target excursion [] n).mass ≤ 8
#guard (target excursion [] 12).mass = 8

-- Explicit blank outputs are discarded, while false data bits remain observable.
#guard (source excursion [] 3).output = #[none, none, none]
#guard (target excursion [] 3).output = #[]
#guard (target excursion [] 4).output = #[false]

-- Input movement stays at both boundaries and resumes inward on the next opposite move.
#guard ((List.range 8).map fun n ↦ (target excursion [true, false] n).inputPos.val) =
  [1, 0, 0, 1, 2, 3, 3, 2]
#guard ((List.range 8).map fun n ↦ (target excursion [] n).inputPos.val) =
  [1, 0, 0, 1, 1, 1, 1, 0]

private def halted := { excursion with q₀ := 12 }

#guard (List.range 4).all (agrees halted [false])
#guard (target halted [false] 3).state.1 = 12
#guard (target halted [false] 3).state.2 () = none
#guard (target halted [false] 3).output = #[]
#guard (target halted [false] 3).inputPos.val = 1
#guard (target halted [false] 3).mass = 0

end Complexity.StackSimulationTest
