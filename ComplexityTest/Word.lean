/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import ComplexityTest.TMRun
meta import ComplexityTest.TMRun

import Complexity.Models.StackMachine.Program.IO
import Complexity.Models.StackMachine.Program.Correctness
import Complexity.Models.StackMachine.TuringMachine
import Complexity.Control.Program.For

meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.For
meta import Complexity.Control.Transition.Basic
meta import Complexity.Data.IntMemory.Basic
meta import Complexity.Data.IntMemory.List
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.StackMachine.Configuration
meta import Complexity.Models.StackMachine.Basic
meta import Complexity.Models.StackMachine.Program.Basic
meta import Complexity.Models.StackMachine.Program.Word
meta import Complexity.Models.StackMachine.Program.IO
meta import Complexity.Models.StackMachine.Program.Correctness
meta import Complexity.Models.StackMachine.TuringMachine

open ComplexityTest Complexity Complexity.TM

namespace WordTests

def source : List Bool := [false, true, false]

-- Raw input bits are copied without a delimiter, including false bits and the empty input.
def stackMatches (m : IntMemory (Option Bool)) (cached : Option Bool) (word : List Bool) : Bool :=
  let stored := if cached.isSome then word.tail else word
  (cached.isNone || cached == word.head?) &&
    (List.range 32).all fun i ↦ m[(i : ℤ) - 4] == (StackMachine.Tape.encode stored)[(i : ℤ) - 4]

def checkLoad (word : List Bool) (suffix : List Bool := []) : Bool :=
  let xs := word.toArray.map some
  let p : StackMachine.Program (Fin 3) Bool Unit := StackMachine.Program.IO.load 0 1
  let M := p.compile.toTM
  let c₀ := M.init xs.toList
  let c : Cfg (Fin 3) (Option Bool) xs :=
    { c₀.2 with
      workTapes := fun j ↦ if j = 0 then StackMachine.Tape.encode suffix
        else if j = 2 then StackMachine.Tape.encode source else ∅
      workPos := fun j ↦ if j = 0 then suffix.length else if j = 2 then source.length else 0
      output := #[some false, none, some true] }
  let steps := 6 * word.length + 4
  let d :=
    if word.length ≤ 1 then M.runFrom (c₀.1, c) steps else TMRun.runFrom M (c₀.1, c) steps
  M.halt d.1 && (d.2.inputPos.val == xs.size + 1) && (d.2.output == c.output) &&
    (d.2.workPos 0 == (word ++ suffix).length) && (d.2.workPos 1 == 0) &&
    (d.2.workPos 2 == source.length) &&
    stackMatches (d.2.workTapes 0) (d.1.2 0) (word ++ suffix) &&
    stackMatches (d.2.workTapes 1) (d.1.2 1) [] &&
    stackMatches (d.2.workTapes 2) (d.1.2 2) source

#guard checkLoad []
#guard checkLoad [false]
#guard checkLoad [true]
#guard checkLoad [false, true, true, false, false, true]
#guard checkLoad [false, true] [true, false]

-- The backend performs simultaneous operations and keeps an empty pop at address zero.
def checkStackAction : Bool :=
  let a : StackMachine.Action (Fin 3) Bool :=
    { inputMove := 1
      work := fun i ↦ if i = 1 then .push false else .pop
      output := some false }
  let p := StackMachine.Program.act a
  let M := p.compile.toTM
  let c : StackMachine.Cfg (Fin 3) Bool #[true, false] :=
    { inputPos := 1, output := #[true]
      «stacks» := fun i ↦ if i = 0 then [] else if i = 1 then [true] else [false, true] }
  let d := M.runFrom (M.q₀, c.toTM (fun _ ↦ false)) 1
  M.halt d.1 && d.2.inputPos.val == 2 && d.2.output == #[some true, some false] &&
    d.2.workPos 0 == 0 && d.2.workPos 1 == 2 && d.2.workPos 2 == 1 &&
    stackMatches (d.2.workTapes 0) (d.1.2 0) [] &&
    stackMatches (d.2.workTapes 1) (d.1.2 1) [false, true] &&
    stackMatches (d.2.workTapes 2) (d.1.2 2) [true]

#guard checkStackAction

-- Shared checks retain partial external I/O and inspect every stack, including erased cells.
def checkStacks (p : StackMachine.Program (Fin 3) Bool Unit)
    (before after : Fin 3 → List Bool) (steps : ℕ) : Bool :=
  let M := p.compile.toTM
  let c : StackMachine.Cfg (Fin 3) Bool #[true, false, true] :=
    { inputPos := 2, output := #[true, false], «stacks» := before }
  let d := TMRun.runFrom M (M.q₀, c.toTM (fun _ ↦ false)) steps
  M.halt d.1 && d.2.inputPos.val == 2 && d.2.output == #[some true, some false] &&
    (List.finRange 3).all fun i ↦
      d.2.workPos i == (after i).length && stackMatches (d.2.workTapes i) (d.1.2 i) (after i)

-- Generic copying restores its source and scratch, and retains the target's old suffix.
def checkStackCopy (word suffix : List Bool) : Bool :=
  checkStacks (StackMachine.Program.Word.copy 0 1 2)
    (fun i ↦ if i = 0 then word else if i = 1 then suffix else [])
    (fun i ↦ if i = 0 then word else if i = 1 then word ++ suffix else [])
    (6 * word.length + 4)

#guard checkStackCopy [] [true]
#guard checkStackCopy [false] []
#guard checkStackCopy [false, true, false] [true, false]

-- Clearing removes false and true bits, preserving both unrelated nonempty stacks.
def checkStackClear (word : List Bool) : Bool :=
  checkStacks (StackMachine.Program.Word.clear 0)
    (fun i ↦ if i = 0 then word else source)
    (fun i ↦ if i = 0 then [] else source) (3 * word.length + 2)

#guard checkStackClear []
#guard checkStackClear [false]
#guard checkStackClear [true]
#guard checkStackClear [false, true, false, true]

-- Reuse storage repeatedly, then write a shorter result without leaving stale cells.
def reuse : StackMachine.Program (Fin 3) Bool Unit := do
  Program.forFin fun _ : Fin 3 ↦ do
    StackMachine.Program.Word.clear 0
    StackMachine.Program.Word.copy 1 0 2
  StackMachine.Program.Word.clear 0
  StackMachine.Program.push 0 true

#guard checkStacks reuse
  (fun i ↦ if i = 0 then [true, false, true, false, true, false] else if i = 1 then source else [])
  (fun i ↦ if i = 0 then [true] else if i = 1 then source else []) 512

end WordTests
