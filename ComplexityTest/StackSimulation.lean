/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.StackMachine.FromTuringMachine
import Complexity.Models.StackMachine.TuringMachine
import Complexity.Models.TuringMachine.Nondeterministic.Basic
meta import Complexity.Models.StackMachine.FromTuringMachine
meta import Complexity.Models.StackMachine.TuringMachine
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
  transition q v := pure <| (q + 1,
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
      output := some (if q == 0 then v.1 else v.2 ()) })

private def source (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) :=
  M.run (xs.map some) n

private def target (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) :=
  M.toStack.run xs n

private def agrees (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) : Bool :=
  let c := source M xs n
  let d := target M xs n
  (c.1.val, c.2.inputPos.val, c.2.workSymbols (), c.2.output.toList.filterMap id) ==
    (d.1.1.val, d.2.inputPos.val, d.1.2 (), d.2.output.toList)

-- Compare the actual bounded runs, including every intermediate state and halted padding.
#guard (List.range 16).all (agrees excursion [true, false])
#guard (List.range 16).all (agrees excursion [])
#guard (source excursion [true, false] 12).2.workPos () = 2
#guard (target excursion [true, false] 12).2.output = #[true, false, true, false, true, false]
#guard (List.range 16).all fun n ↦ (target excursion [] n).2.mass ≤ 8
#guard (target excursion [] 12).2.mass = 8

-- Explicit blank outputs are discarded, while false data bits remain observable.
#guard (source excursion [] 3).2.output = #[none, none, none]
#guard (target excursion [] 3).2.output = #[]
#guard (target excursion [] 4).2.output = #[false]

-- Input movement stays at both boundaries and resumes inward on the next opposite move.
#guard ((List.range 8).map fun n ↦ (target excursion [true, false] n).2.inputPos.val) =
  [1, 0, 0, 1, 2, 3, 3, 2]
#guard ((List.range 8).map fun n ↦ (target excursion [] n).2.inputPos.val) =
  [1, 0, 0, 1, 1, 1, 1, 0]

private def halted := { excursion with q₀ := 12 }

#guard (List.range 4).all (agrees halted [false])
#guard (target halted [false] 3).1.1 = 12
#guard (target halted [false] 3).1.2 () = none
#guard (target halted [false] 3).2.output = #[]
#guard (target halted [false] 3).2.inputPos.val = 1
#guard (target halted [false] 3).2.mass = 0

-- Guess a bit twice; the second guess changes only the tape, so its branches coincide in output.
private def guess : NTM Unit (Option Bool) (Fin 3) where
  q₀ := 0
  halt q := q == 2
  transition q _ i := (q + 1,
    { inputMove := 0
      work := fun _ ↦ (some (some (i == 1)), 1)
      output := some (if q == 0 then some (i == 1) else none) })

private def branchOutputs (n : ℕ) : Multiset (List Bool) :=
  (guess.runWith Multiset [some true] n).map (·.2.output.toList.filterMap id)

private def stackBranchOutputs (n : ℕ) : Multiset (List Bool) :=
  (guess.toStack.runWith Multiset [true] n).map (·.2.output.toList)

-- Every branch is simulated once, so coincident branches keep their multiplicities.
#guard (List.range 5).all fun n ↦ stackBranchOutputs n = branchOutputs n
#guard stackBranchOutputs 3 = {[false], [false], [true], [true]}

-- Guards that one simulation lemma gives both the deterministic and the branching statement.
example (M : TM Id Unit (Option Bool) (Fin 13)) (xs : List Bool) (n : ℕ) :
    TM.Stack.HistRep (M.runHistory (xs.map some) n) (M.toStack.runHistory xs n) :=
  (TM.liftRel_runHistoryWith_toStack Id M xs n).run

example (M : NTM Unit (Option Bool) (Fin 3)) (xs : List Bool) (n : ℕ) :
    Multiset.Rel TM.Stack.HistRep
      (M.runHistoryWith Multiset (xs.map some) n) (M.toStack.runHistoryWith Multiset xs n) :=
  (TM.liftRel_runHistoryWith_toStack Multiset M xs n).multisetRel

-- Guards that a computation of a nondeterministic Turing machine passes along to the stack
-- machine on `Multiset`, with the source outputs written as `.ntm` writes them.
example {κ Q : Type} [Fintype κ] (M : NTM κ (Option Bool) Q) (xs : List Bool)
    (outs : Multiset (List Bool)) (t s : ℕ)
    (h : M.ComputesInWith Multiset (xs.map some) (outs.map (·.map some))
      Controller.History.length Controller.History.space t s) :
    M.toStack.ComputesInWith Multiset xs outs Controller.History.length
      (fun h ↦ h.configSup StackMachine.Cfg.mass) t (2 * s) :=
  h.toStack

-- Guess a bit and push it, guess and push again, then pop. The target keeps a pushed top in
-- control and writes it to the tape at the next push; the output records the observed tops, so
-- the third guess only doubles the branches.
private def stackGuess : StackMachine BinaryChoice Unit Bool (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q v i := (q + 1,
    { inputMove := 0
      work := fun _ ↦ if q == 2 then .pop else .push (i == 1)
      output := if q == 0 then none else v.2 () })

private def stackGuessOutputs (n : ℕ) : Multiset (List Bool) :=
  (stackGuess.runWith Multiset [true] n).map (·.2.output.toList)

private def tmGuessOutputs (n : ℕ) : Multiset (List Bool) :=
  (stackGuess.toTM.runWith Multiset [some true] n).map (·.2.output.toList.filterMap id)

-- Every stack branch is simulated by exactly one tape branch, keeping multiplicities.
#guard (List.range 5).all fun n ↦ tmGuessOutputs n = stackGuessOutputs n
#guard tmGuessOutputs 3 =
  {[false, false], [false, false], [false, true], [false, true],
    [true, false], [true, false], [true, true], [true, true]}

-- Guards that a computation of a nondeterministic stack machine passes along to the Turing
-- machine on `Multiset`.
example {κ Q : Type} [Fintype κ] (M : StackMachine BinaryChoice κ Bool Q) (xs : List Bool)
    (outs : Multiset (List Bool)) (t s : ℕ)
    (h : M.ComputesInWith Multiset xs outs Controller.History.length
      (fun h ↦ h.configSup StackMachine.Cfg.mass) t s) :
    M.toTM.ComputesInWith Multiset (xs.map some) (outs.map (·.map some))
      Controller.History.length Controller.History.space t (Fintype.card κ * (s + 1)) :=
  h.toTM

end Complexity.StackSimulationTest
