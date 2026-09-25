/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Cost
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Control.Transition.Cost
meta import Complexity.Data.Tree
import Mathlib.Data.Fin.VecNotation
meta import Mathlib.Data.Fin.VecNotation

open Complexity Complexity.TreeMachine

namespace Complexity.TreeMachineTest

def a : Complexity.Tree := Tree.pair Tree.nil Tree.nil

def b : Complexity.Tree := Tree.pair a Tree.nil

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
#guard grow.cost c 1 = 7
#guard grow.cost c 20 = 7
#guard grow.timeUsed c 20 = 1
#guard Controller.runConfigMaxFrom grow TreeMachine.treeCosts.space c 20 = 13
#guard ((grow.runFromWithCost treeCosts.time (Choice.Interpretation.id Id) c 20).run).2 = 7

-- Writing an empty leaf costs one even when it replaces a larger tree.
def shrink : TreeMachine Id 3 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign true (.left 0 2)

#guard (shrink.step c).mass = 5
#guard (shrink.step c).regs 1 = a
#guard shrink.cost c 20 = 1
#guard Controller.runConfigMaxFrom shrink TreeMachine.treeCosts.space c 20 = 9

-- Fully expanded destination size is charged even if the runtime can share subtrees.
def double : TreeMachine Id 1 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| Action.assign false (.pair 0 0 0)

#guard Tree.size ((double.run (Config := Cfg 1 Bool) Tree.nil 6).regs 0) = 127
#guard double.runActionSum treeCosts.time Tree.nil 6 = 246
#guard double.runActionSum (Config := Cfg 1 Bool) (fun _ _ => 1) Tree.nil 6 = 6
#guard double.runConfigMax (Config := Cfg 1 Bool) treeCosts.space Tree.nil 6 = 127

-- An active identity transition still costs one; an initially halted machine costs zero.
def idle (q : Bool) : TreeMachine Id 0 Bool where
  q₀ := q
  halt := id
  transition _ _ := pure <| Action.keep false

#guard (idle false).cost (Cfg.mk (idle false).q₀ Fin.elim0) 5 = 5
#guard (idle true).cost (Cfg.mk (idle true).q₀ Fin.elim0) 5 = 0
#guard (idle true).timeUsed (Cfg.mk (idle true).q₀ Fin.elim0) 5 = 0
#guard Controller.runConfigMaxFrom (idle true) TreeMachine.treeCosts.space
  (Cfg.mk (idle true).q₀ Fin.elim0) 5 = 0

-- `nop` preserves a register bank while changing the selected control state.
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).regs 0 = a
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).regs 1 = b
#guard (apply (Action.assign true (.nop : Op 2)) (Cfg.mk false ![a, b])).state

-- Branch multiplicity and failure have the same semantics as in the multi-tape model.
def fork : TreeMachine Choice.Binary 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := Action.assign true (.pair 0 0 0)

#guard ((fork.runWith (Config := Cfg 1 Bool) Choice.binaryMultiset Tree.nil 5).map (fun c ↦ c.regs 0)) = ↑[a, a]
#guard ((fork.runFromWithCost treeCosts.time Choice.binaryMultiset
  (fork.initInput (Config := Cfg 1 Bool) Tree.nil) 5).map Prod.snd) = ↑[3, 3]

-- Two `nop` branches remain distinct effects, even though their resulting banks agree.
def forkNop : TreeMachine Choice.Binary 1 Bool where
  q₀ := false
  halt := id
  transition _ _ _ := Action.assign true .nop

#guard ((forkNop.runWith (Config := Cfg 1 Bool) Choice.binaryMultiset b 5).map (fun c ↦ c.regs 0)) = ↑[b, b]
#guard ((forkNop.runFromWithCost treeCosts.time Choice.binaryMultiset
  (forkNop.initInput (Config := Cfg 1 Bool) b) 5).map Prod.snd) = ↑[1, 1]

-- Shrinking to a nonempty tree still pays for that entire tree.
#guard treeCosts.time (Action.assign true (.left 0 0)) c = 3

-- Equal endpoints can have different fees: a no-op and writing back the same tree.
def sameEndpoint : TreeMachine Choice.Binary 3 Bool where
  q₀ := false
  halt := id
  transition _ _ i := if i = 0 then Action.keep true else Action.assign true (.pair 0 1 2)

#guard ((sameEndpoint.runFromWithCost treeCosts.time Choice.binaryMultiset c 5).map
  (fun (d, fee) ↦ (d.state, d.regs 0, fee))) = ↑[(true, b, 1), (true, b, 5)]

-- Two fresh choices reach all four leaves, including paths 01 and 10.
def twoChoices : TreeMachine Choice.Binary 0 (Fin 7) where
  q₀ := 0
  halt q := decide (3 ≤ q.val)
  transition q _ i := Action.keep ⟨(2 * q.val + 1 + i.val) % 7, Nat.mod_lt _ (by decide)⟩

#guard ((twoChoices.runFromWith Choice.binaryMultiset (Cfg.mk twoChoices.q₀ Fin.elim0) 2).map
  (fun c ↦ c.state.val)) = ↑[3, 4, 5, 6]

-- A successful `nop` is different from failure in `Option`.
def optionNop : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := some (Action.assign true .nop)

#guard (optionNop.runFromWith (Choice.Interpretation.id Option)
  (Cfg.mk optionNop.q₀ Fin.elim0) 1).isSome
#guard ((optionNop.runFromWith (Choice.Interpretation.id Option)
  (Cfg.mk optionNop.q₀ Fin.elim0) 1).map
  (fun c ↦ c.state)) = some true

def abort : TreeMachine Option 0 Bool where
  q₀ := false
  halt := id
  transition _ _ := none

#guard (abort.runFromWith (Choice.Interpretation.id Option)
  (Cfg.mk abort.q₀ Fin.elim0) 0).isSome
#guard (abort.runFromWith (Choice.Interpretation.id Option)
  (Cfg.mk abort.q₀ Fin.elim0) 1).isNone
#guard (abort.runFromWith (Choice.Interpretation.id Option)
  (⟨true, Fin.elim0⟩ : Cfg 0 Bool) 10).isSome

end Complexity.TreeMachineTest
