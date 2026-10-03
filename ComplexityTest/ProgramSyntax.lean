/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.Program.Loop
import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Transition.Basic
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory.Basic
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration

open Complexity (TM Program)
open Complexity.TM

namespace ProgramSyntaxTest

abbrev Code := Program Unit Unit Unit (fun _ : Unit ↦ Unit)

-- Program can be stored and returned as ordinary data in Type.
structure Box : Type where
  code : Code Unit

example : Type := Array (Code Unit)
example : Code (Code Unit) := pure (pure ())

-- Compile with the public backend and check the first halting time, not padded execution.
def check {k : ℕ} (p : TM.Program (Fin k) (Fin 2) Unit) (xs ys : Array (Fin 2)) (n : ℕ) : Bool :=
  let M := p.compile
  let c := M.run (Cfg (Fin k) _ _ xs.toList.toArray) xs.toList n
  M.halt c.state && c.output == ys && (n == 0 || !M.halt (M.run (Cfg (Fin k) _ _ xs.toList.toArray) xs.toList (n - 1)).state)

-- One continuation is pure; the other has two internal actions and a different state type.
def branch : TM.Program (Fin 0) (Fin 2) Unit := do
  let i ← Program.readInput
  if i == 0 then pure () else do
    Program.emit 1
    Program.emit 0
  Program.emit i

#guard check branch #[0] #[0] 2
#guard check branch #[1] #[1, 0, 1] 4

-- Snapshot the bank, recover a function of its components, and inspect that result.
def bank (a : Fin 2) : TM.Program (Fin 3) (Fin 2) Unit := do
  Program.write 0 1
  Program.write 2 a
  let v ← Program.observeBits fun v (i : Fin 3) ↦ v.2 i == 1
  let f := fun i : Fin 3 ↦ if v[i] then (1 : Fin 2) else 0
  Program.emit (if f 0 == f 2 && f 1 == 0 then 1 else 0)

#guard check (bank 0) #[] #[0] 4
#guard check (bank 1) #[] #[1] 4

-- Different finite types index dispatchers and final exits. The returned exit value is used.
def body (i : Fin 3) : TM.Program (Fin 0) (Fin 2) (Fin 3 ⊕ Fin 2) := do
  Program.emit (Fin.ofNat 2 i.val)
  pure (if i == 2 then .inr 1 else .inl (i + 1))

def loop : TM.Program (Fin 0) (Fin 2) Unit := do
  let i ← Program.loopOn Program.idle body 0
  Program.emit i

-- Three dispatches, three body emissions, and one emission after the loop.
#guard check loop #[] #[0, 1, 0, 1] 7

end ProgramSyntaxTest
