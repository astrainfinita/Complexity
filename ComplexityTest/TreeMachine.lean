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
def project : Action 2 Bool := Action.assign true (.right 0 0)

def afterProject : Cfg 2 Bool := apply project ⟨false, ![Tree.pair a b, a]⟩

#guard afterProject.regs 0 = b
#guard afterProject.regs 1 = a

-- Reading another register preserves it; only the selected destination changes.
def afterLeft : Cfg 2 Bool :=
  apply (Action.assign (k := 2) true (.left 1 0)) ⟨false, ![Tree.pair a b, Tree.nil]⟩

#guard afterLeft.regs 0 = Tree.pair a b
#guard afterLeft.regs 1 = a

def grow : TreeMachine Id 3 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign true (.pair 1 1 1)

-- Arbitrary register inputs belong to the configuration-level process API.
def growInput : Cfg 3 Bool := Cfg.mk grow.q₀ (input 1 a)
#guard growInput.regs 0 = Tree.nil
#guard growInput.regs 1 = a
#guard growInput.regs 2 = Tree.nil
#guard (grow.runFrom growInput 1).regs 1 = Tree.pair a a
#guard (grow.runFrom growInput 1).regs 0 = Tree.nil

def c : Cfg 3 Bool := Cfg.mk grow.q₀ ![b, a, Tree.nil]

#guard c.mass = 9
#guard (grow.step c).mass = 13
#guard (grow.step c).regs 0 = b
#guard (grow.step c).regs 2 = Tree.nil
#guard (grow.runHistoryFrom c 1).actionSum Action.timeCost = 7
#guard (grow.runHistoryFrom c 20).actionSum Action.timeCost = 7
#guard (grow.runHistoryFrom c 20).length = 1
#guard (grow.runHistoryFrom c 20).configSup Cfg.mass = 13

-- Writing an empty leaf costs one even when it replaces a larger tree.
def shrink : TreeMachine Id 3 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign true (.left 0 2)

#guard (shrink.step c).mass = 5
#guard (shrink.step c).regs 1 = a
#guard (shrink.runHistoryFrom c 20).actionSum Action.timeCost = 1
#guard (shrink.runHistoryFrom c 20).configSup Cfg.mass = 9

-- Fully expanded destination size is charged even if the runtime can share subtrees.
def double : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign false (.pair 0 0 0)

#guard Tree.size ((double.run (Cfg 1 Bool) Tree.nil 6).regs 0) = 127
#guard (double.runHistory _ Tree.nil 6).actionSum Action.timeCost = 246
#guard (double.runHistory (Cfg 1 Bool) Tree.nil 6).length = 6
#guard (double.runHistory (Cfg 1 Bool) Tree.nil 6).configSup Cfg.mass = 127

-- An active identity transition still costs one; an initially halted machine costs zero.
def idle (q : Bool) : TreeMachine Id 0 Bool where
  q₀ := q
  halt := id
  transition _ _ := pure <| Action.keep false

#guard ((idle false).runHistoryFrom (Cfg.mk (idle false).q₀ Fin.elim0) 5).actionSum
  Action.timeCost = 5
#guard ((idle true).runHistoryFrom (Cfg.mk (idle true).q₀ Fin.elim0) 5).actionSum
  Action.timeCost = 0
#guard ((idle true).runHistoryFrom (Cfg.mk (idle true).q₀ Fin.elim0) 5).length = 0
#guard ((idle true).runHistoryFrom (Cfg.mk (idle true).q₀ Fin.elim0) 5).configSup Cfg.mass = 0

-- `nop` preserves a register bank while changing the selected control state.
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).regs 0 = a
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).regs 1 = b
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).state

-- Branch multiplicity and failure have the same semantics as in the multi-tape model.
def fork : TreeMachine BinaryChoice 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := Action.assign true (.pair 0 0 0)

#guard ((fork.runWith (Cfg 1 Bool) Multiset Tree.nil 5).map (fun c ↦ c.regs 0)) = ↑[a, a]
#guard ((fork.runHistoryWith (Cfg 1 Bool) Multiset Tree.nil 5).map
  (fun h ↦ h.actionSum Action.timeCost)) = ↑[3, 3]

-- Two `nop` branches remain distinct effects, even though their resulting banks agree.
def forkNop : TreeMachine BinaryChoice 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := Action.assign true .nop

#guard ((forkNop.runWith (Cfg 1 Bool) Multiset b 5).map (fun c ↦ c.regs 0)) = ↑[b, b]
#guard ((forkNop.runHistoryWith (Cfg 1 Bool) Multiset b 5).map
  (fun h ↦ h.actionSum Action.timeCost)) = ↑[1, 1]

-- Shrinking to a nonempty tree still pays for that entire tree.
#guard Action.timeCost (Action.assign true (.left 0 0)) c = 3

-- Equal endpoints can have different fees: a no-op and writing back the same tree.
def sameEndpoint : TreeMachine BinaryChoice 3 Bool where
  q₀ := false
  halt := id
  transition _ _ i := if i = 0 then Action.keep true else Action.assign true (.pair 0 1 2)

#guard ((sameEndpoint.runHistoryFromWith Multiset c 5).map
  (fun h ↦ (h.last.state, h.last.regs 0, h.actionSum Action.timeCost))) = ↑[(true, b, 1), (true, b, 5)]

-- Two fresh choices reach all four leaves, including paths 01 and 10.
def twoChoices : TreeMachine BinaryChoice 0 (Fin 7) where
  q₀ := 0
  halt q := decide (3 ≤ q.val)
  transition q _ i := Action.keep ⟨(2 * q.val + 1 + i.val) % 7, Nat.mod_lt _ (by decide)⟩

#guard ((twoChoices.runFromWith Multiset (Cfg.mk twoChoices.q₀ Fin.elim0) 2).map
  (fun c ↦ c.state.val)) = ↑[3, 4, 5, 6]

-- A successful `nop` is different from failure in `Option`.
def optionNop : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := some (Action.assign true .nop)

#guard (optionNop.runFromWith Option
  (Cfg.mk optionNop.q₀ Fin.elim0) 1).isSome
#guard ((optionNop.runHistoryFromWith Option
  (Cfg.mk optionNop.q₀ Fin.elim0) 1).map
  (fun h ↦ (h.last.state, h.length))) = some (true, 1)

def abort : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := none

#guard ((abort.runHistoryFromWith Option
  (Cfg.mk abort.q₀ Fin.elim0) 0).map (fun h ↦ (h.last.state, h.length))) = some (false, 0)
#guard (abort.runFromWith Option
  (Cfg.mk abort.q₀ Fin.elim0) 1).isNone
#guard (abort.runHistoryFromWith Option
  (Cfg.mk abort.q₀ Fin.elim0) 1).isNone
#guard (abort.runFromWith Option
  (⟨true, Fin.elim0⟩ : Cfg 0 Bool) 10).isSome
#guard ((abort.runHistoryFromWith Option
  (⟨true, Fin.elim0⟩ : Cfg 0 Bool) 10).map (fun h ↦ h.length)) = some 0

end Complexity.TreeMachineTest
