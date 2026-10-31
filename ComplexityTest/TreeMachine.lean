/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice.Basic
meta import Complexity.Control.BinaryChoice.Basic
import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Cost
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Control.Controller.RunHistory
meta import Complexity.Control.Controller.History.Basic
meta import Complexity.Control.Controller.History.Cost
meta import Complexity.Data.Tree.Basic
import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation

open Complexity Complexity.TreeMachine

namespace Complexity.TreeMachineTest

def a : Tree := Tree.pair Tree.nil Tree.nil

def b : Tree := Tree.pair a Tree.nil

-- An operation reads the old destination when its source aliases it.
def project : Action 2 := .right 0 0

def afterProject : Cfg 2 := apply project ⟨![Tree.pair a b, a]⟩

#guard afterProject.regs 0 = b
#guard afterProject.regs 1 = a

-- Reading another register preserves it; only the selected destination changes.
def afterLeft : Cfg 2 :=
  apply (Action.left (k := 2) 1 0) ⟨![Tree.pair a b, Tree.nil]⟩

#guard afterLeft.regs 0 = Tree.pair a b
#guard afterLeft.regs 1 = a

def grow : TreeMachine Id 3 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (true, .pair 1 1 1)

-- Arbitrary register inputs belong to the configuration-level process API.
def growInput : Bool × Cfg 3 := (grow.q₀, Cfg.mk (input 1 a))
#guard growInput.2.regs 0 = Tree.nil
#guard growInput.2.regs 1 = a
#guard growInput.2.regs 2 = Tree.nil
#guard (grow.runFrom growInput 1).2.regs 1 = Tree.pair a a
#guard (grow.runFrom growInput 1).2.regs 0 = Tree.nil

def c : Bool × Cfg 3 := (grow.q₀, Cfg.mk ![b, a, Tree.nil])

#guard c.2.mass = 9
#guard (grow.step c).2.mass = 13
#guard (grow.step c).2.regs 0 = b
#guard (grow.step c).2.regs 2 = Tree.nil
#guard (grow.runHistoryFrom c 1).snd.actionSum Action.sizeCost = 7
#guard (grow.runHistoryFrom c 20).snd.actionSum Action.sizeCost = 7
#guard (grow.runHistoryFrom c 20).length = 1
#guard (grow.runHistoryFrom c 20).snd.configSup Cfg.mass = 13

-- Reading an empty source costs one even when it replaces a larger destination.
def shrink : TreeMachine Id 3 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (true, .left 0 2)

#guard (shrink.step c).2.mass = 5
#guard (shrink.step c).2.regs 1 = a
#guard (shrink.runHistoryFrom c 20).snd.actionSum Action.sizeCost = 1
#guard (shrink.runHistoryFrom c 20).snd.configSup Cfg.mass = 9

-- Fully expanded destination size is charged even if the runtime can share subtrees.
def double : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| (false, .pair 0 0 0)

#guard Tree.size ((double.run Tree.nil 6).2.regs 0) = 127
#guard (double.runHistory Tree.nil 6).snd.actionSum Action.sizeCost = 246
#guard (double.runHistory Tree.nil 6).length = 6
#guard (double.runHistory Tree.nil 6).snd.configSup Cfg.mass = 127

-- An active identity transition still costs one; an initially halted machine costs zero.
def idle (q : Bool) : TreeMachine Id 0 Bool where
  q₀ := q
  halt := id
  transition _ _ := pure <| (false, .nop)

#guard ((idle false).runHistoryFrom ((idle false).q₀, Cfg.mk Fin.elim0) 5).snd.actionSum
  Action.sizeCost = 5
#guard ((idle true).runHistoryFrom ((idle true).q₀, Cfg.mk Fin.elim0) 5).snd.actionSum
  Action.sizeCost = 0
#guard ((idle true).runHistoryFrom ((idle true).q₀, Cfg.mk Fin.elim0) 5).length = 0
#guard ((idle true).runHistoryFrom ((idle true).q₀, Cfg.mk Fin.elim0) 5).snd.configSup Cfg.mass = 0

-- `nop` preserves a register bank while changing the selected control state.
#guard (apply ((true, .nop) : Bool × Action 2) (false, Cfg.mk ![a, b])).2.regs 0 = a
#guard (apply ((true, .nop) : Bool × Action 2) (false, Cfg.mk ![a, b])).2.regs 1 = b
#guard (apply ((true, .nop) : Bool × Action 2) (false, Cfg.mk ![a, b])).1

-- Branch multiplicity and failure have the same semantics as in the multi-tape model.
def fork : TreeMachine BinaryChoice 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := (true, .pair 0 0 0)

#guard (fork.runWith Multiset Tree.nil 5).map (fun c ↦ c.2.regs 0) = ↑[a, a]
#guard (fork.runHistoryWith Multiset Tree.nil 5).map
  (fun h ↦ h.snd.actionSum Action.sizeCost) = ↑[3, 3]

-- Two `nop` branches remain distinct effects, even though their resulting banks agree.
def forkNop : TreeMachine BinaryChoice 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := (true, .nop)

#guard (forkNop.runWith Multiset b 5).map (fun c ↦ c.2.regs 0) = ↑[b, b]
#guard (forkNop.runHistoryWith Multiset b 5).map
  (fun h ↦ h.snd.actionSum Action.sizeCost) = ↑[1, 1]

-- A projection pays for the entire source, including the child it discards.
#guard Action.sizeCost (.left 0 0 : Action 3) c.2 = 5

-- Equal endpoints can have different fees: a no-op and writing back the same tree.
def sameEndpoint : TreeMachine BinaryChoice 3 Bool where
  q₀ := false
  halt := id
  transition _ _ i := if i = 0 then (true, .nop) else (true, .pair 0 1 2)

#guard (sameEndpoint.runHistoryFromWith Multiset c 5).map
  (fun h ↦ (h.last.1, h.last.2.regs 0, h.snd.actionSum Action.sizeCost)) =
    ↑[(true, b, 1), (true, b, 5)]

-- Two fresh choices reach all four leaves, including paths 01 and 10.
def twoChoices : TreeMachine BinaryChoice 0 (Fin 7) where
  q₀ := 0
  halt q := decide (3 ≤ q.val)
  transition q _ i := (⟨(2 * q.val + 1 + i.val) % 7, Nat.mod_lt _ (by decide)⟩, .nop)

#guard (twoChoices.runFromWith Multiset (twoChoices.q₀, Cfg.mk Fin.elim0) 2).map
  (fun c ↦ c.1.val) = ↑[3, 4, 5, 6]

-- A successful `nop` is different from failure in `Option`.
def optionNop : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := some (true, .nop)

#guard (optionNop.runFromWith Option
  (optionNop.q₀, Cfg.mk Fin.elim0) 1).isSome
#guard (optionNop.runHistoryFromWith Option
  (optionNop.q₀, Cfg.mk Fin.elim0) 1).map
  (fun h ↦ (h.last.1, h.length)) = some (true, 1)

def abort : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := none

#guard (abort.runHistoryFromWith Option
  (abort.q₀, Cfg.mk Fin.elim0) 0).map (fun h ↦ (h.last.1, h.length)) = some (false, 0)
#guard (abort.runFromWith Option
  (abort.q₀, Cfg.mk Fin.elim0) 1).isNone
#guard (abort.runHistoryFromWith Option
  (abort.q₀, Cfg.mk Fin.elim0) 1).isNone
#guard (abort.runFromWith Option
  ((true, ⟨Fin.elim0⟩) : Bool × Cfg 0) 10).isSome
#guard (abort.runHistoryFromWith Option
  ((true, ⟨Fin.elim0⟩) : Bool × Cfg 0) 10).map (fun h ↦ h.length) = some 0

end Complexity.TreeMachineTest
