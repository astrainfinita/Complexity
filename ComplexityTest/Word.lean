/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Word.Clear
import Complexity.Models.TuringMachine.Program.Word.Write
import Complexity.Models.TuringMachine.Program.Word.IO
import Complexity.Control.Program.For

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.For
meta import Complexity.Control.Transition
meta import Complexity.Data.IntMemory
meta import Complexity.Data.IntMemory.List
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Seek
meta import Complexity.Models.TuringMachine.Program.Word.Basic
meta import Complexity.Models.TuringMachine.Program.Word.Write
meta import Complexity.Models.TuringMachine.Program.Word.Copy
meta import Complexity.Models.TuringMachine.Program.Word.Rewind
meta import Complexity.Models.TuringMachine.Program.Word.Append
meta import Complexity.Models.TuringMachine.Program.Word.Clear
meta import Complexity.Models.TuringMachine.Program.Word.IO

open Complexity Complexity.TM

namespace WordTests

def input : Array (Option Bool) := #[some true, none, some false]

def source : List Bool := [false, true, false]

-- Both tape indices are Boolean. Input and output are already partially consumed/produced.
def initial (p : Program Bool (Option Bool) Unit) (word : List Bool)
    (pos otherPos : ℤ) : Cfg Bool (Option Bool) (p.State ⊕ p.Exit) input :=
  { (p.compile.initInput (Config := Cfg Bool _ _ input.toList.toArray) input.toList) with
    inputPos := 2
    workTapes := fun j ↦ Program.Word.tape (if j then source else word)
    workPos := fun j ↦ if j then otherPos else pos
    output := #[some false, none, some true] }

-- Inspect a region extending beyond every old and new word, including the left blank.
def tapeMatches (m : IntMemory (Option Bool)) (word : List Bool) : Bool :=
  (List.range 32).all fun i ↦ m[(i : ℤ) - 4] == (Program.Word.tape word)[(i : ℤ) - 4]

def check (p : Program Bool (Option Bool) Unit) (before after : List Bool)
    (pos finalPos otherPos finalOtherPos : ℤ) : Bool :=
  let c := initial p before pos otherPos
  let d := p.compile.runFrom c 512
  p.compile.halt d.state && (d.inputPos == c.inputPos) && (d.output == c.output) &&
    (d.workPos false == finalPos) && (d.workPos true == finalOtherPos) &&
    tapeMatches (d.workTapes false) after && tapeMatches (d.workTapes true) source

-- Rewinding from home must first cross the left blank, even for a nonempty word.
#guard check (Program.Word.rewind false) [] [] 0 0 2 2
#guard [0, 1].all fun p ↦ check (Program.Word.rewind false) [false] [false] p 0 2 2
#guard [0, 1, 2, 4].all fun p ↦ check (Program.Word.rewind false)
  [false, true, false, true] [false, true, false, true] p 0 2 2

-- Reverse erasure must remove false bits as well as true bits, leaving no stale suffix.
#guard check (Program.Word.clear false) [] [] 0 0 2 2
#guard check (Program.Word.clear false) [false] [] 0 0 2 2
#guard check (Program.Word.clear false) [true] [] 0 0 2 2
#guard check (Program.Word.clear false) [false, true, false, true] [] 0 0 2 2

-- Copying a suffix advances both heads; appending restores only the source head.
#guard check (Program.Word.copy false true) [true] [true, true, false] 1 3 1 3
#guard check (Program.Word.append false true) [true] [true, false, true, false] 1 4 0 0

-- Repeated reuse alternates clearing, appending, and rewinding before a shorter final write.
def reuse : Program Bool (Option Bool) Unit := do
  Complexity.Program.forFin fun _ : Fin 3 ↦ do
    Program.Word.clear false
    Program.Word.append false true
    Program.Word.rewind false
  Program.Word.clear false
  Program.Word.put false (some true)
  Program.Word.rewind false

#guard check reuse [true, false, true, false, true, false] [true] 0 0 0 0

-- Raw input bits are copied without a delimiter, including false bits and the empty input.
def checkLoad (word : List Bool) : Bool :=
  let xs := word.toArray.map some
  let p : Program Bool (Option Bool) Unit := Program.Word.load false
  let c : Cfg Bool (Option Bool) (p.State ⊕ p.Exit) xs :=
    { (p.compile.initInput (Config := Cfg Bool _ _ xs.toList.toArray) xs.toList) with
      workTapes := fun j ↦ Program.Word.tape (if j then source else [])
      workPos := fun j ↦ if j then 2 else 0
      output := #[some false, none, some true] }
  let d := p.compile.runFrom c (6 * word.length + 6)
  p.compile.halt d.state && (d.inputPos.val == xs.size + 1) && (d.output == c.output) &&
    (d.workPos false == 0) && (d.workPos true == 2) &&
    tapeMatches (d.workTapes false) word && tapeMatches (d.workTapes true) source

#guard checkLoad []
#guard checkLoad [false]
#guard checkLoad [true]
#guard checkLoad [false, true, true, false, false, true]

end WordTests
