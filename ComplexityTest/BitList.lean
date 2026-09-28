/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Simulation.BitList

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Enumeration
meta import Complexity.Control.Program.For
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Transition
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory
meta import Complexity.Data.IntMemory.List
meta import Complexity.Data.NatMemory
meta import Complexity.Data.Tree
meta import Complexity.Data.Tree.BitList
meta import Complexity.Data.Tree.Encoding
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Models.TreeMachine.Encoding
meta import Complexity.Models.TreeMachine.Program.Pair
meta import Complexity.Models.TreeMachine.Program.Project
meta import Complexity.Models.TreeMachine.Program.Scan
meta import Complexity.Models.TreeMachine.Simulation.BitList
meta import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
meta import Complexity.Models.TreeMachine.Simulation.BitList.Input
meta import Complexity.Models.TreeMachine.Simulation.BitList.Output
meta import Complexity.Models.TreeMachine.Simulation.Layout
meta import Complexity.Models.TreeMachine.Simulation.Program.Compiler
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Call.Buffered
meta import Complexity.Models.TuringMachine.Program.Enumeration
meta import Complexity.Models.TuringMachine.Program.Move
meta import Complexity.Models.TuringMachine.Program.Seek
meta import Complexity.Models.TuringMachine.Program.Word.Append
meta import Complexity.Models.TuringMachine.Program.Word.Basic
meta import Complexity.Models.TuringMachine.Program.Word.Clear
meta import Complexity.Models.TuringMachine.Program.Word.Configuration
meta import Complexity.Models.TuringMachine.Program.Word.Copy
meta import Complexity.Models.TuringMachine.Program.Word.IO
meta import Complexity.Models.TuringMachine.Program.Word.Rewind
meta import Complexity.Models.TuringMachine.Program.Word.Write
meta import Complexity.Models.TuringMachine.RedirectInput
meta import Complexity.Models.TuringMachine.RedirectOutput
meta import Complexity.Models.TuringMachine.Tapes
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

-- One fixed finite TM computes identity on every raw list, including [] and [false].
example (xs : List Bool) :
    (compiler identity).ComputesInTimeAndSpace (xs.map some) (xs.map some)
      (timeBound 1 xs.length 0) (spaceBound 1 xs.length 0) :=
  computesInTimeAndSpace identity (identity_spec xs)

-- Execute the complete input adapter, simulator, and output adapter.
def checkIdentity (xs : List Bool) : Bool :=
  let M := compiler identity
  let c := M.run (TM.Cfg (Fin 3 ⊕ Bool) _ _ (xs.map some).toArray) (xs.map some) 1024
  M.halt c.state && c.output == xs.toArray.map some

#guard checkIdentity []
#guard checkIdentity [false, true, false]

end Complexity.BitListTest
