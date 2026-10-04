/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Simulation.BitList.Correctness

meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Enumeration
meta import Complexity.Control.Program.For
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Transition.Basic
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory.Basic
meta import Complexity.Data.IntMemory.List
meta import Complexity.Data.NatMemory
meta import Complexity.Data.Tree.Basic
meta import Complexity.Data.Tree.BitList
meta import Complexity.Data.Tree.Encoding
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Models.TreeMachine.Simulation.BitList.Correctness
meta import Complexity.Models.TreeMachine.Simulation.Basic
meta import Complexity.Models.TreeMachine.Simulation.Build
meta import Complexity.Models.TreeMachine.Simulation.Bank
meta import Complexity.Models.TreeMachine.Simulation.Init
meta import Complexity.Models.TreeMachine.Simulation.Correctness
meta import Complexity.Models.TreeMachine.StackProgram
meta import Complexity.Models.StackMachine.Configuration
meta import Complexity.Models.StackMachine.Basic
meta import Complexity.Models.StackMachine.Program.Basic
meta import Complexity.Models.StackMachine.Program.Word
meta import Complexity.Models.StackMachine.Program.IO
meta import Complexity.Models.StackMachine.Program.Correctness
meta import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
meta import Complexity.Models.TreeMachine.Simulation.BitList.Input
meta import Complexity.Models.TreeMachine.Simulation.BitList.Output
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Data.Embedding

open Complexity Complexity.TreeMachine
open Complexity.TreeMachine.Simulation.BitList

namespace Complexity.BitListTest

-- The user's example uses the tree serialization 1011000.
example : BitList.encodeTree (Tree.encodeBitList [false, true]) =
    [true, false, true, true, false, false, false] := rfl

-- A trailing false bit remains distinct from the empty list.
example : Tree.encodeBitList [] ≠ Tree.encodeBitList [false] := by
  intro h
  have := Tree.encodeBitList_injective h
  contradiction

example : payload [false, true] =
    BitList.encodeTree (Tree.encodeBitList [false, true]) :=
  payload_eq_encodeTree _

def identity : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| Action.keep ()

theorem identity_spec (xs : List Bool) :
    identity.ComputesInTimeAndSpace (Tree.encodeBitList xs)
      (Tree.encodeBitList xs) 0 (Tree.encodeBitList xs).size := by
  refine ⟨0, rfl, ?_, le_rfl, ?_⟩
  · change TreeMachine.input (0 : Fin 1) (Tree.encodeBitList xs) 0 = _
    simp
  · simp [TreeMachine.Cfg.mass]

-- One fixed finite stack machine computes identity on every raw list, including [] and [false].
example (xs : List Bool) :
    (compiler identity).ComputesInTimeAndSpace xs xs
      (timeBound 1 xs.length 0) (Simulation.spaceBound 1 (Tree.encodeBitList xs).size) :=
  computesInTimeAndSpace identity (identity_spec xs)

-- Execute all three stages, including initially halted and nontrivial source runs.
def check (M : TreeMachine Id 1 Bool) (xs ys : List Bool) : Bool :=
  let N := compiler M
  let c := N.run (StackMachine.Cfg (Simulation.Work 1) Bool _ xs.toArray) xs 2048
  N.halt c.state && c.output == ys.toArray

def halted : TreeMachine Id 1 Bool where
  q₀ := true
  halt := id
  transition _ _ := pure <| Action.assign false (.pair 0 0 0)

def tail : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign true (.right 0 0)

#guard check halted [] []
#guard check halted [false] [false]
#guard check halted [true] [true]
#guard check halted [false, true, false] [false, true, false]
#guard check tail [] []
#guard check tail [true, false, true] [false, true]

end Complexity.BitListTest
