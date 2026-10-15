/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Language.Nat
import Complexity.Resources.TreeMachine.Program
import ComplexityTest.TreeRun
meta import ComplexityTest.TreeRun
meta import Complexity.Models.TreeMachine.Language.Compiler
meta import Complexity.Models.TreeMachine.Language.Nat

open Complexity TreeProgram TreeProgram.Code

namespace Complexity.TreeProgramLibraryTest

-- The source list proof gives a machine bound, including input/output setup and retained locals.
example (x : Tree) :
    (List.Code.reverse .input).compile.ComputesInUnitTimeAndSpace x (x.reverseAppend .nil)
      (13 * x.listLength + 12) ((List.Code.reverse .input).registers * (x.size + 3)) := by
  have h := List.Code.reverse_bounded .input 1 (Function.update (fun _ ↦ Tree.nil) 0 x)
  exact (h.mono le_rfl le_rfl (fun _ _ h ↦ h.1)).compile (by simp)

-- One ordinary source program computes Nat.succ on every encoded natural number.
private theorem succ_computable :
    TimeSpaceModel.tree.ComputableWithin Nat.succ (fun a ↦ 28 * (encode Tree a).size + 29)
      (fun a ↦ (Nat.Code.succ .input).registers * ((encode Tree a).size + 7)) := by
  apply Code.computableWithin (Nat.Code.succ .input) Nat.succ
    (fun a ↦ 28 * (encode Tree a).size + 25) (fun a ↦ (encode Tree a).size + 5)
  · intro a
    refine (Nat.Code.succ_bounded _ _ _ a ?_).mono ?_ le_rfl (fun _ _ h ↦ h.1)
    · simp
    · have hl : a.bits.length ≤ (encode Tree a).size := Tree.length_le_size_encodeBitList a.bits
      omega
  · intro a; omega

-- The already established conversion handles size charges; source proofs only use unit time.
example : TimeSpaceModel.sizeCostTree.ComputableWithin Nat.succ
    (fun a ↦ (28 * (encode Tree a).size + 29) *
      ((Nat.Code.succ .input).registers * ((encode Tree a).size + 7)))
    (fun a ↦ (Nat.Code.succ .input).registers * ((encode Tree a).size + 7)) :=
  succ_computable.toSizeCost

-- Two calls compose at the source level without inspecting either generated program.
def addTwo (x : Value) : Code Value := do
  Nat.Code.succ (← Nat.Code.succ x)

private theorem addTwo_bounded (x : Value) (n : ℕ) (s : ℕ → Tree) (a : ℕ)
    (hx : x.eval s = encode Tree a) :
    (addTwo x).Bounded n s (56 * a.bits.length + 78) ((encode Tree a).size + 9)
      (fun v t ↦ v.eval t = encode Tree (a + 2)) := by
  have hlen : (a + 1).bits.length ≤ a.bits.length + 1 := by
    simpa using BitList.length_increment_le a.bits
  have hsize : (encode Tree (a + 1)).size ≤ (encode Tree a).size + 4 := by
    simpa only [BitList.increment_bits, encode_nat_tree] using size_encode_increment_le a.bits
  unfold addTwo
  rw [show 56 * a.bits.length + 78 =
    (28 * a.bits.length + 25) + (28 * a.bits.length + 53) by omega]
  apply Bounded.bind ((Nat.Code.succ_bounded x n s a hx).mono le_rfl (by omega)
    (fun _ _ h ↦ h.1))
  intro y t hy
  apply (Nat.Code.succ_bounded y _ t (a + 1) hy).mono (by omega) (by omega)
  intro v u hv
  simpa [Nat.add_assoc] using hv.1

private theorem addTwo_computable :
    TimeSpaceModel.tree.ComputableWithin (fun a : ℕ ↦ a + 2)
      (fun a ↦ 56 * (encode Tree a).size + 82)
      (fun a ↦ (addTwo .input).registers * ((encode Tree a).size + 11)) := by
  apply Code.computableWithin (addTwo .input) (fun a : ℕ ↦ a + 2)
    (fun a ↦ 56 * (encode Tree a).size + 78) (fun a ↦ (encode Tree a).size + 9)
  · intro a
    refine (addTwo_bounded _ _ _ a ?_).mono ?_ le_rfl (fun _ _ h ↦ h)
    · simp
    · have hl : a.bits.length ≤ (encode Tree a).size := Tree.length_le_size_encodeBitList a.bits
      omega
  · intro a; omega

example : TimeSpaceModel.sizeCostTree.ComputableWithin (fun a : ℕ ↦ a + 2)
    (fun a ↦ (56 * (encode Tree a).size + 82) *
      ((addTwo .input).registers * ((encode Tree a).size + 11)))
    (fun a ↦ (addTwo .input).registers * ((encode Tree a).size + 11)) :=
  addTwo_computable.toSizeCost


-- The last failed loop test costs two transitions even when the body never runs.
example (s : Unit → Tree) : (Cmd.while .nil .skip).Run s 2 s 1 := .while_false rfl

-- The empty and nonempty branches share the same one-transition root test.
example (s : ℕ → Tree) (v : Value) :
    (ifNode v (pure ()) (pure ())).Bounded 1 s 1 (v.eval s).size (fun _ _ ↦ True) := by
  simpa using Bounded.ifNode v (pure ()) (pure ()) (fun _ _ ↦ True) le_rfl
    (time := 0) (by simp) (by simp)

private def finished (p : Code Value) (x y : Tree) (steps : ℕ) : Bool :=
  let c := ComplexityTest.TreeRun.runFrom p.compile
    (p.compile.initInput (Config := TreeMachine.Cfg p.registers _) x) steps
  p.compile.halt c.state && decide (c.regs 0 = y)

#guard finished (Nat.Code.succ .input) (encode Tree (0 : ℕ)) (encode Tree (1 : ℕ)) 29

#guard finished (Nat.Code.succ .input) (encode Tree (1 : ℕ)) (encode Tree (2 : ℕ)) 57
#guard finished (Nat.Code.succ .input) (encode Tree (3 : ℕ)) (encode Tree (4 : ℕ)) 85
#guard finished (Nat.Code.succ .input) (encode Tree (2 : ℕ)) (encode Tree (3 : ℕ)) 29
#guard BitList.decodeNat [false] == none
#guard BitList.decodeNat [true, false] == none
#guard BitList.decodeNat [false, true] == some 2

-- Mapping an ordinary helper invokes its runtime loop for each element, without host unrolling.
#guard finished (List.Code.map Nat.Code.succ .input)
  (encode Tree ([0, 3] : List ℕ)) (encode Tree ([1, 4] : List ℕ)) 250

/-- A small reduction-generator shape: enumerate cells, assign binary identifiers and emit
raw tree templates. This deliberately makes no choice of a formula or literal encoding. -/
def numberedCells (xs : Value) : Code Value := do
  let index ← newVar .nil
  let cells ← newVar .nil
  List.Code.forEach xs fun row ↦ do
    List.Code.forEach xs fun col ↦ do
      let i ← read index
      let payload ← row.pair col
      let cell ← i.pair payload
      write cells (← cell.pair (← read cells))
      write index (← Nat.Code.succ i)
  List.Code.reverse (← read cells)

private def cell (i row col : ℕ) : Tree :=
  .pair (encode Tree i) (.pair (encode Tree row) (encode Tree col))

#guard finished (numberedCells .input) (encode Tree ([] : List ℕ)) (encode Tree ([] : List Tree)) 100
#guard finished (numberedCells .input) (encode Tree ([0, 1] : List ℕ))
  (encode Tree [cell 0 0 0, cell 1 0 1, cell 2 1 0, cell 3 1 1]) 600

end Complexity.TreeProgramLibraryTest
