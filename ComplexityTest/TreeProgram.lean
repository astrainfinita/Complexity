/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TreeMachine.Language.Compiler
import Complexity.Models.TreeMachine.Language.Verification
meta import Complexity.Models.TreeMachine.Language.Compiler

open Complexity TreeProgram TreeProgram.Code

namespace Complexity.TreeProgramTest

-- Ordinary definitions and ordinary `do`: no generated declarations or command elaborator.
def nestedAssignment (xs : Value) : Code Value := do
  let value ← newVar xs
  let old ← read value
  write value (.pair old.left (.pair old.right old))
  read value

def snapshot (xs : Value) : Code Value := do
  let value ← newVar xs
  let old ← read value
  write value .nil
  pure old

-- Both branches allocate locals, with different construction lengths.
def branchLocals (xs : Value) : Code Value := do
  let result ← newVar .nil
  ifNode xs
    (do let temp ← newVar xs; write result (← read temp))
    (do
      let temp ← newVar (.pair .nil .nil)
      let copy ← newVar (← read temp)
      write result (← read copy))
  read result

-- A snapshot outside a loop survives local allocations and writes inside the loop.
def loopSnapshot (xs : Value) : Code Value := do
  let value ← newVar xs
  let old ← read value
  whileNode value do
    let empty ← newVar .nil
    write value (← read empty)
  pure old

def choose (xs : Value) : Code Value := do
  let result ← newVar .nil
  ifNode xs (write result xs.left) (write result (.pair .nil .nil))
  read result

-- Definitions compose through bind, with the same value semantics as other Lean monads.
def swapChildren (xs : Value) : Code Value := pure (.pair xs.right xs.left)

def swapTwice (xs : Value) : Code Value := do
  let swapped ← swapChildren xs
  swapChildren swapped

def reverseBody (rest acc : Var) : Code Unit := do
  let r ← read rest
  let a ← read acc
  write acc (.pair r.left a)
  write rest r.right

def reverse (xs : Value) : Code Value := do
  let rest ← newVar xs
  let acc ← newVar .nil
  whileNode rest (reverseBody rest acc)
  read acc

def reverseAux : Tree → Tree → Tree
  | .nil, acc => acc
  | .pair head rest, acc => reverseAux rest (.pair head acc)

def followRight (xs : Value) : Code Value := do
  let rest ← newVar xs
  whileNode rest do
    let r ← read rest
    write rest r.right
  read rest

def nestedLoops (xs : Value) : Code Value := do
  let outer ← newVar xs
  whileNode outer do
    let value ← read outer
    let inner ← newVar value.left
    whileNode inner do
      let value ← read inner
      write inner value.right
    write outer value.right
  read outer

-- Proofs use source execution rules, independently of allocation to machine registers.
theorem nestedAssignment_correct (x : Tree) :
    (nestedAssignment .input).Computes x (.pair x.left (.pair x.right x)) := by
  simp [computes_iff, nestedAssignment, Var.get]

theorem snapshot_correct (x : Tree) : (snapshot .input).Computes x x := by
  simp [computes_iff, snapshot, Var.get]

theorem branchLocals_correct (x : Tree) :
    (branchLocals .input).Computes x (if x.root then x else .pair .nil .nil) := by
  cases h : x.root <;> simp [computes_iff, branchLocals, h]

theorem loopSnapshot_correct (x : Tree) : (loopSnapshot .input).Computes x x := by
  simp [computes_iff, loopSnapshot]
  cases h : x.root with
  | false =>
    refine ⟨_, _, ⟨(), Exec.whileNode_false _ _ (by simpa using h)⟩, ?_⟩
    simp
  | true =>
    refine ⟨_, _, ⟨(), Exec.whileNode_true _ _ (by simpa using h)
      (by simp; rfl) (Exec.whileNode_false _ _ (by simp))⟩, ?_⟩
    simp

theorem choose_correct (x : Tree) :
    (choose .input).Computes x (if x.root then x.left else .pair .nil .nil) := by
  cases x <;> simp [computes_iff, choose, Var.get, Tree.root]

theorem swapTwice_correct (x : Tree) :
    (swapTwice .input).Computes x (.pair x.left x.right) := by
  simp [computes_iff, swapTwice, swapChildren]

private theorem reverseBody_total (rest acc : Var) (n : ℕ)
    (ha : acc.index < n) (hne : rest ≠ acc) (y : Tree) (k : ℕ) :
    (reverseBody rest acc).Total n
      (fun s ↦ reverseAux (rest.get s) (acc.get s) = y ∧
        (rest.get s).root = true ∧ (rest.get s).size = k)
      (fun _ s ↦ reverseAux (rest.get s) (acc.get s) = y ∧ (rest.get s).size < k) := by
  have hne' : rest.index ≠ acc.index := fun h ↦ hne (Var.ext h)
  intro s ⟨hI, hroot, hn⟩
  simp [reverseBody]
  cases he : rest.get s with
  | nil => simp [he] at hroot
  | node label head tail =>
    cases label
    simp only [he, Tree.size_pair] at hn
    simp only [Var.get] at *
    simp_all [ha.ne, ha.ne.symm, hne'.symm, reverseAux]
    omega

private theorem reverseLoop_total (rest acc : Var) (n : ℕ)
    (ha : acc.index < n) (hne : rest ≠ acc) (y : Tree) :
    (whileNode rest (reverseBody rest acc)).Total n
      (fun s ↦ reverseAux (rest.get s) (acc.get s) = y) (fun _ s ↦ acc.get s = y) := by
  apply (Total.whileNode rest (reverseBody rest acc)
    (fun s ↦ reverseAux (rest.get s) (acc.get s) = y) (fun s ↦ (rest.get s).size)
    (reverseBody_total rest acc n ha hne y)).consequence (fun _ h ↦ h)
  intro _ s ⟨hI, hstop⟩
  simpa [Tree.root_eq_false.mp hstop, reverseAux] using hI

theorem reverse_correct (x : Tree) :
    (reverse .input).Computes x (reverseAux x .nil) := by
  simp [computes_iff, reverse]
  apply reverseLoop_total <;> first | decide | simp [Var.get]

-- Source correctness transfers to the machine without inspecting generated code.
example (x : Tree) :
    let p := reverse .input
    ∃ n, p.compile.Halted (p.compile.run (TreeMachine.Cfg p.registers _) x n) ∧
      (p.compile.run (TreeMachine.Cfg p.registers _) x n).regs 0 = reverseAux x .nil :=
  Code.compile_correct (reverse_correct x)

example (p : Code Value) : Finite (p.source.close.code.State ⊕ p.source.close.code.Exit) :=
  inferInstance

private def leafPair : Tree := .pair .nil .nil

private def finished (p : Code Value) (x y : Tree) (n : ℕ) : Bool :=
  let c := p.compile.run (TreeMachine.Cfg p.registers _) x n
  p.compile.halt c.state && decide (c.regs 0 = y)

#guard finished (snapshot .input) leafPair leafPair 30
#guard finished (choose .input) .nil leafPair 30
#guard finished (choose .input) leafPair .nil 30
#guard finished (swapTwice .input) leafPair leafPair 30
#guard finished (reverse .input) .nil .nil 30
#guard finished (do
  let v ← newVar .input
  whileNode v (write v .nil)
  read v) leafPair .nil 30

end Complexity.TreeProgramTest
