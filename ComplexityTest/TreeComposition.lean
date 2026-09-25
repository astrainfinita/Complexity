/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Composition
meta import Complexity.Models.TreeMachine.Composition
meta import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Cost
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Control.Transition.Cost
meta import Complexity.Data.Tree

open Complexity Complexity.TreeMachine

namespace Complexity.TreeCompositionTest

def a : Tree := .pair .nil .nil

-- Leave both scratch registers dirty, and return a nonempty intermediate result.
def dirty : TreeMachine Id 3 (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ := pure <|
    if q = 0 then Action.assign 1 (.pair 1 0 0)
    else if q = 1 then Action.assign 2 (.pair 2 0 0)
    else Action.assign 3 (.pair 0 0 0)

-- The output is correct only when every scratch register starts empty.
def needsClean (k : ℕ) [NeZero k] : TreeMachine Id k Bool where
  q₀ := false
  halt := id
  transition _ roots := pure <|
    if ∃ i : Fin k, i ≠ 0 ∧ roots i = true then Action.assign true (.pair 0 0 0)
    else Action.assign true (.left 0 0)

def halted (k : ℕ) : TreeMachine Id k Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| Action.keep ()

-- A larger destination shares the old work bank and gains one fresh scratch slot.
def wider := dirty.comp (needsClean 4)

#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 3).regs 0 =
    .pair a a
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 3).regs 1 =
    .pair a a
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 3).regs 2 =
    .pair a a
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 4).regs 1 =
    .pair a a
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 5).regs 1 = .nil
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 5).regs 2 =
    .pair a a
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 6).regs 2 = .nil
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 7).regs 3 = .nil
#guard ∀ n : Fin 5, (wider.run
    (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a (3 + n.val)).regs 0 = .pair a a
#guard ¬wider.Halted (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 7)
#guard wider.Halted (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 8)
#guard (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 8).regs 0 = a

-- The reserved slot stays empty through both phases, cleanup, and halted padding.
#guard ∀ n : Fin 16, (wider.run
    (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a n.val).regs 4 = .nil

-- Cleanup costs exactly K, including the initial control transfer.
#guard wider.cost (wider.run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) a 3) 4 = 4
#guard wider.runActionSum treeCosts.time a 20 = 28
#guard wider.runActionSum
    (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) (fun _ _ => 1) a 20 = 8
#guard wider.runConfigMax
    (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 (Fin 4) Bool)) treeCosts.space a 20 = 23

-- A smaller destination also clears the old scratch slot it does not itself use.
def narrower := dirty.comp (needsClean 2)

#guard narrower.Halted (narrower.run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) a 7)
#guard (narrower.run (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) a 7).regs 0 = a
#guard (narrower.run (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) a 7).regs 1 = .nil
#guard (narrower.run (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) a 7).regs 2 = .nil
#guard ∀ n : Fin 16, (narrower.run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) a n.val).regs 3 = .nil
#guard narrower.runActionSum treeCosts.time a 20 = 27
#guard narrower.runConfigMax
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Bool)) treeCosts.space a 20 = 22

-- Initially halted endpoints still perform the bridge, including the K = 1 case.
#guard (dirty.comp (halted 2)).Halted ((dirty.comp (halted 2)).run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Unit)) a 6)
#guard ((dirty.comp (halted 2)).run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Unit)) a 6).regs 0 = .pair a a
#guard ((dirty.comp (halted 2)).run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Unit)) a 6).regs 1 = .nil
#guard ((dirty.comp (halted 2)).run
    (Config := Cfg (max 3 2 + 1) (Comp.State 3 2 (Fin 4) Unit)) a 6).regs 2 = .nil
#guard (dirty.comp (halted 2)).runActionSum treeCosts.time a 20 = 24
#guard ((halted 3).comp (needsClean 4)).Halted (((halted 3).comp (needsClean 4)).run (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 Unit Bool)) a 5)
#guard (((halted 3).comp (needsClean 4)).run
    (Config := Cfg (max 3 4 + 1) (Comp.State 3 4 Unit Bool)) a 5).regs 0 = .nil
#guard ¬((halted 1).comp (halted 1)).Halted (((halted 1).comp (halted 1)).run
    (Config := Cfg (max 1 1 + 1) (Comp.State 1 1 Unit Unit)) a 0)
#guard ((halted 1).comp (halted 1)).Halted (((halted 1).comp (halted 1)).run
    (Config := Cfg (max 1 1 + 1) (Comp.State 1 1 Unit Unit)) a 1)
#guard (((halted 1).comp (halted 1)).run
    (Config := Cfg (max 1 1 + 1) (Comp.State 1 1 Unit Unit)) a 1).regs 0 = a
#guard ((halted 1).comp (halted 1)).runActionSum treeCosts.time a 20 = 1

private theorem dirty_computes : dirty.ComputesInTimeAndSpace a (.pair a a) 21 21 := by
  refine ⟨3, rfl, rfl, ?_, ?_⟩ <;> decide

private theorem needsClean_computes :
    (needsClean 4).ComputesInTimeAndSpace (.pair a a) a 3 10 := by
  refine ⟨1, rfl, rfl, ?_, ?_⟩ <;> decide

-- The public composition bound agrees with the concrete execution above.
example : wider.ComputesInTimeAndSpace a a 28 23 :=
  comp_computesInTimeAndSpace dirty (needsClean 4) dirty_computes needsClean_computes

end Complexity.TreeCompositionTest
