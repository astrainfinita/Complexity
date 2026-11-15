/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import all Init.Data.List.Scan.Basic
import Complexity.Resources.TreeMachine.Composition
meta import Complexity.Models.TreeMachine.Composition
meta import Complexity.Models.TreeMachine.Deterministic
meta import Complexity.Models.TreeMachine.Cost
meta import Complexity.Models.TreeMachine.Basic
meta import Complexity.Models.TreeMachine.Configuration
meta import Complexity.Data.Tree.Basic

open Complexity Complexity.TreeMachine

namespace Complexity.TreeCompositionTest

def a : Tree := .pair .nil .nil

-- Leave both scratch registers dirty, and return a nonempty intermediate result.
def dirty : TreeMachine Id 3 (Fin 4) where
  q₀ := 0
  halt q := q == 3
  transition q _ := pure <|
    if q = 0 then (1, .pair 1 0 0)
    else if q = 1 then (2, .pair 2 0 0)
    else (3, .pair 0 0 0)

-- The output is correct only when every scratch register starts empty.
def needsClean (k : ℕ) [NeZero k] : TreeMachine Id k Bool where
  q₀ := false
  halt := id
  transition _ roots := pure <|
    if ∃ i : Fin k, i ≠ 0 ∧ roots i = true then (true, .pair 0 0 0)
    else (true, .left 0 0)

def halted (k : ℕ) : TreeMachine Id k Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| ((), .nop)

-- A larger destination shares the old work bank and gains one fresh scratch slot.
def wider := dirty.comp (needsClean 4)

#guard (wider.run a 3).2.regs 0 = .pair a a
#guard (wider.run a 3).2.regs 1 = .pair a a
#guard (wider.run a 3).2.regs 2 = .pair a a
#guard (wider.run a 4).2.regs 1 = .pair a a
#guard (wider.run a 5).2.regs 1 = .nil
#guard (wider.run a 5).2.regs 2 = .pair a a
#guard (wider.run a 6).2.regs 2 = .nil
#guard (wider.run a 7).2.regs 3 = .nil
#guard ∀ n : Fin 5, (wider.run
    a (3 + n.val)).2.regs 0 = .pair a a
#guard ¬wider.Halted (wider.run a 7)
#guard wider.Halted (wider.run a 8)
#guard (wider.run a 8).2.regs 0 = a

-- The reserved slot stays empty through both phases, cleanup, and halted padding.
#guard ∀ n : Fin 16, (wider.run
    a n.val).2.regs 4 = .nil

-- Cleanup costs exactly K, including the initial control transfer.
#guard (wider.runHistoryFrom
  (wider.run a 3) 4).snd.actionSum Action.sizeCost = 4
#guard
  let h := (wider.runHistory a 20).snd
  (h.actionSum Action.sizeCost, h.length, h.configSup Cfg.mass) = (32, 8, 23)

-- A smaller destination also clears the old scratch slot it does not itself use.
def narrower := dirty.comp (needsClean 2)

#guard narrower.Halted (narrower.run
    a 7)
#guard (narrower.run a 7).2.regs 0 = a
#guard (narrower.run a 7).2.regs 1 = .nil
#guard (narrower.run a 7).2.regs 2 = .nil
#guard ∀ n : Fin 16, (narrower.run
    a n.val).2.regs 3 = .nil
#guard
  let h := (narrower.runHistory a 20).snd
  (h.actionSum Action.sizeCost, h.configSup Cfg.mass) = (31, 22)

-- Initially halted endpoints still perform the bridge, including the K = 1 case.
#guard (dirty.comp (halted 2)).Halted ((dirty.comp (halted 2)).run
    a 6)
#guard ((dirty.comp (halted 2)).run
    a 6).2.regs 0 = .pair a a
#guard ((dirty.comp (halted 2)).run
    a 6).2.regs 1 = .nil
#guard ((dirty.comp (halted 2)).run
    a 6).2.regs 2 = .nil
#guard ((dirty.comp (halted 2)).runHistory a 20).snd.actionSum
  Action.sizeCost = 24
#guard ((halted 3).comp (needsClean 4)).Halted (((halted 3).comp (needsClean 4)).run a 5)
#guard (((halted 3).comp (needsClean 4)).run
    a 5).2.regs 0 = .nil
#guard ¬((halted 1).comp (halted 1)).Halted (((halted 1).comp (halted 1)).run
    a 0)
#guard ((halted 1).comp (halted 1)).Halted (((halted 1).comp (halted 1)).run
    a 1)
#guard (((halted 1).comp (halted 1)).run
    a 1).2.regs 0 = a
#guard (((halted 1).comp (halted 1)).runHistory a 20).snd.actionSum
  Action.sizeCost = 1

private theorem dirty_computes : dirty.ComputesWithin a (.pair a a) 21 21 := by
  refine .of_halted 3 rfl rfl ?_ ?_ <;> decide

private theorem needsClean_computes :
    (needsClean 4).ComputesWithin (.pair a a) a 7 10 := by
  refine .of_halted 1 rfl rfl ?_ ?_ <;> decide

-- The public composition bound agrees with the concrete execution above.
example : wider.ComputesWithin a a 32 23 :=
  comp_computesWithin dirty (needsClean 4) dirty_computes needsClean_computes

section NonuniqueEncoding

-- Both codes denote the same value. Specifications must handle either code,
-- and a nested call cannot assume that its input is the chosen representative.
local instance : Encoding Tree Unit where
  decode r := ⟨r = .nil ∨ r = .pair .nil .nil, fun _ => ()⟩
  exists_code _ := ⟨.nil, Or.inl rfl, Subsingleton.elim _ _⟩

private theorem halted_growth :
    ∃ t s, Computes (halted 1) (fun _ : Unit => ()) t s ∧
      Dominated t (fun _ => 0) ∧ Dominated s (fun _ => 1) := by
  refine ⟨fun _ => 0, fun _ => 3, ?_, Dominated.refl _, Dominated.const 3⟩
  intro x r hx
  obtain ⟨hr, rfl⟩ := hx
  refine ⟨r, ⟨hr, rfl⟩, .of_halted 0 rfl (input_get (0 : Fin 1) r) le_rfl ?_⟩
  rcases hr with rfl | rfl <;> decide

-- Zero component time leaves the genuine clearing cost in the fixed composite;
-- space still includes padding, and constant substitution needs no size condition.
example : ∃ t s, Computes ((halted 1).comp (halted 1)) (fun _ : Unit => ()) t s ∧
    Dominated t (fun _ => 1) ∧ Dominated s (fun _ => 2) := by
  exact comp_computesInO halted_growth halted_growth

end NonuniqueEncoding

end Complexity.TreeCompositionTest
