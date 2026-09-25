/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Simulation.Program.Correctness
meta import Complexity.Models.TreeMachine.Simulation.Layout
meta import Complexity.Models.TreeMachine.Simulation.Program.Compiler
meta import Complexity.Models.TuringMachine.Program.Word.Append
meta import Complexity.Models.TuringMachine.Program.Word.Basic
meta import Complexity.Models.TuringMachine.Program.Word.Write
meta import Complexity.Models.TuringMachine.Program.Word.Clear
meta import Complexity.Models.TuringMachine.Program.Word.IO
meta import Complexity.Models.TreeMachine.Program.Project
meta import Complexity.Models.TreeMachine.Program.Pair
meta import Complexity.Models.TuringMachine.Program.Word.Copy
meta import Complexity.Models.TuringMachine.Program.Word.Rewind
meta import Complexity.Models.TreeMachine.Program.Scan
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Loop
meta import Complexity.Control.Program.For
meta import Complexity.Models.TreeMachine.Encoding
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Data.Tree.Encoding
meta import Complexity.Data.Tree
meta import Complexity.Data.IntMemory
import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation

open Complexity TreeMachine TreeMachine.Simulation Std.WP

namespace CompilerTests

def a : Tree := .pair .nil .nil
def b : Tree := .pair a .nil

def once (p : Op 2) : TreeMachine Id 2 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| ⟨p, true⟩

-- Check the actual controller, including input consumption and counter restoration.
def check {k : ℕ} {Q : Type} [FinEnum Q] (M : TreeMachine Id k Q) (i : Fin k) (x : Tree)
    (o : Fin k) (t : Tree) : Bool :=
  let N := TM.Program.compile (Simulation.Program.program M i o)
  let xs := TreeMachine.code x
  let c := N.run (TM.Cfg _ _ _ xs.toArray) xs 4802
  N.halt c.state && (c.output == (TreeMachine.code t).toArray) &&
    (c.inputPos.val == xs.length + 1) && (c.workPos (Compiler.counter k) == 0)

-- Keeping a register copies its original value into the other bank.
#guard check (once .nop) 0 a 0 a
#guard check (once .nop) 1 b 1 b
#guard check (once .nop) 1 b 0 .nil
#guard check (once .nop) 1 .nil 1 .nil

-- Both projections are total at nil and stop at the correct nested-subtree boundary.
#guard check (once (.left 0 0)) 0 .nil 0 .nil
#guard check (once (.right 0 0)) 0 .nil 0 .nil
#guard check (once (.left 0 1)) 1 b 0 a
#guard check (once (.right 0 0)) 0 (Tree.pair a b) 0 b

-- Pairing can copy the same source twice, including when source and destination indices agree.
#guard check (once (.pair 0 0 0)) 0 a 0 (Tree.pair a a)
#guard check (once (.pair 0 1 0)) 1 b 0 (Tree.pair b .nil)

-- A step preserves every register except its single selected destination.
#guard check (once (.pair 0 1 0)) 1 b 1 b
#guard check (once (.right 1 0)) 0 b 0 b
#guard check (once (.right 1 0)) 0 b 1 .nil

-- A later operation observes the value written by the preceding source step.
def twice : TreeMachine Id 2 (Fin 3) where
  q₀ := 0
  halt q := q == 2
  transition q _ := pure <|
    if q = 0 then Action.assign 1 (.right 0 0)
    else Action.assign 2 (.left 1 0)

#guard check twice 0 (Tree.pair b a) 0 a
#guard check twice 0 (Tree.pair b a) 1 .nil

-- Reusing both banks must erase stale suffixes, restore the counter, and observe the new roots.
def thrice : TreeMachine Id 1 (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q r := pure <|
    if q = 0 then Action.assign 1 (.pair 0 0 0)
    else if q = 1 then Action.assign 2 (.right 0 0)
    else Action.assign 3 (if r 0 then .right 0 0 else .pair 0 0 0)

#guard check thrice 0 a 0 .nil
#guard check thrice 0 .nil 0 a

-- An initially halted source still loads and emits; its transition must never execute.
def halted : TreeMachine Id 1 Bool where
  q₀ := true
  halt := id
  transition _ _ := pure <| Action.assign false (.pair 0 0 0)

#guard check halted 0 b 0 b

example : Fintype (Option Bool) := inferInstance
example : Finite (Simulation.Program.program (once .nop) 0 0).State := inferInstance

-- The process theorem starts at the supplied state and can emit a nonzero register.
-- Here the controller starts running at false, but the represented source is already halted.
example (x : Tree) :
    Std.WP.Triple
      ((Complexity.Program.loopOn TM.Program.idle
        (Simulation.Program.body (once .nop) 1) (true, false)).verify
        (TM.Program.cfgSemantics (TreeMachine.code x).toArray))
      (fun c t ↦ c = Simulation.Program.loadedCfg 1 x ∧ 3 * (x.size + 2) + 3 ≤ t)
      (fun _ c _ ↦ c.output = (TreeMachine.code x).toArray) () := by
  let r : Cfg 2 Bool := Cfg.mk true (TreeMachine.input 1 x)
  have hr : Simulation.Program.Rep r false (Simulation.Program.loadedCfg 1 x)
      (x.size + 2) := by
    refine ⟨rfl, rfl, fun _ ↦ [], rfl, ?_⟩
    simp
  have hh : (once .nop).Halted r := rfl
  have hn : ∀ j < 0, ¬(once .nop).Halted ((once .nop).runFrom r j) := by
    intro j hj
    omega
  have ha : ((once .nop).runFrom r 0).regs 1 = x := by
    simp [r,  TreeMachine.input]
  have hm : ∀ j ≤ 0, ((once .nop).runFrom r j).mass ≤ x.size + 2 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    change (∑ i, (TreeMachine.input (1 : Fin 2) x i).size) ≤ _
    rw [sum_size_input]
    omega
  simpa only [Nat.zero_mul, Nat.zero_add, r] using
    Simulation.Program.spec_loop (once .nop) r 1
      (Simulation.Program.loadedCfg 1 x) false x 0 (x.size + 2) hr hh hn ha hm

-- The public compiler exposes binary I/O and the complete resource theorem.
example {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q] (M : TreeMachine Id k Q)
    (x a : Tree) (t s : ℕ) (h : M.ComputesInTimeAndSpace x a t s) :
    (compiler M).ComputesInTimeAndSpace (TreeMachine.code x) (TreeMachine.code a)
      (Compiler.timeBound k x.size t) (Compiler.spaceBound k x.size t) :=
  Compiler.computesInTimeAndSpace M h

end CompilerTests
