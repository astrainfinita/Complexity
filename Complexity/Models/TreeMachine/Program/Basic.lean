/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Complexity.Control.Program.Semantics
public import Complexity.Control.Program.Compiler

/-! # Finite programs over tree registers -/

@[expose] public section

namespace Complexity.TreeMachine

namespace Program

/-- Instructions return only finite observations; tree values remain in registers. -/
inductive Op (k : ℕ) where
  | act (o : TreeMachine.Action k)
  | root (i : Fin k)

/-- A write returns unit; a root test returns a Boolean. -/
abbrev Op.Result {k : ℕ} : Op k → Type
  | .act _ => Unit
  | .root _ => Bool

instance {k : ℕ} (o : Op k) : Finite o.Result := by
  cases o <;> dsimp [Op.Result] <;> infer_instance

end Program

/-- Finite control over tree-register instructions and root observations, with choices of the
shape `F` (`Id` for deterministic programs). -/
protected abbrev Program (F : Type → Type) (k : ℕ) :=
  Program F (Fin k → Bool) (TreeMachine.Action k) (Program.Op k) Program.Op.Result

namespace Program

variable {F : Type → Type} {k : ℕ}

/-- Reading a root emits a no-op and consumes one transition. -/
def eval : (o : Op k) → (Fin k → Bool) → TreeMachine.Action k × o.Result
  | .act o, _ => (o, ())
  | .root i, v => (.nop, v i)

/-- Execute one register instruction. -/
def act (o : TreeMachine.Action k) : TreeMachine.Program F k Unit :=
  Program.perform (Op.act o)

/-- Read whether a register contains a node. -/
def root (i : Fin k) : TreeMachine.Program F k Bool :=
  Program.perform (Op.root i)

/-- Loop dispatch takes one no-op transition per iteration. -/
def repeatUntil (p : TreeMachine.Program F k Bool) : TreeMachine.Program F k Unit :=
  Program.repeatUntilWith .nop p

/-- Select a finite value under the choice shape `F`, in one no-op transition. -/
def choose [Functor F] {β : Type} [FinEnum β] (c : F β) : TreeMachine.Program F k β :=
  Program.chooseWith .nop c

/-- Copy a tree through a temporary pair; the auxiliary register need not be empty. -/
def copy (aux dst src : Fin k) : TreeMachine.Program Id k Unit := do
  act (.pair dst src aux)
  act (.left dst dst)

/-- Compile a program to a machine with the same choice shape, the tree operation interpreter and
`nop` for the exits. Each action takes one step. -/
def compile [Functor F] [Pure F] {α : Type} (p : TreeMachine.Program F k α) :
    TreeMachine F k (p.State ⊕ p.Exit) :=
  Program.Syntax.compile eval .nop p

end Program
end Complexity.TreeMachine
