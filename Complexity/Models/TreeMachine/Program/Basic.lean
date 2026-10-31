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

/-- Finite control over tree-register instructions and root observations. -/
protected abbrev Program (k : ℕ) :=
  Program (Fin k → Bool) (TreeMachine.Action k) (Program.Op k) Program.Op.Result

namespace Program

variable {k : ℕ}

/-- Reading a root emits a no-op and consumes one transition. -/
def eval : (o : Op k) → (Fin k → Bool) → TreeMachine.Action k × o.Result
  | .act o, _ => (o, ())
  | .root i, v => (.nop, v i)

/-- Execute one register instruction. -/
def act (o : TreeMachine.Action k) : TreeMachine.Program k Unit :=
  Program.perform (Op.act o)

/-- Read whether a register contains a node. -/
def root (i : Fin k) : TreeMachine.Program k Bool :=
  Program.perform (Op.root i)

/-- Loop dispatch takes one no-op transition per iteration. -/
def repeatUntil (p : TreeMachine.Program k Bool) : TreeMachine.Program k Unit :=
  Program.repeatUntilWith .nop p

/-- Interpret a program on the machine's register bank, without machine control states. -/
@[simps eval observe act]
def semantics :
    Program.Semantics (Fin k → Bool) (TreeMachine.Action k) (Op k) Op.Result (Cfg k) where
  eval := eval
  observe := Controller.observe
  act := Controller.apply

theorem exec_act (o : TreeMachine.Action k) (c : Cfg k) :
    (act o).Exec semantics c 1 () (apply o c) :=
  Program.Exec.perform semantics (.act o) c

theorem exec_root (i : Fin k) (c : Cfg k) :
    (root i).Exec semantics c 1 (c.regs i).root c :=
  Program.Exec.perform semantics (.root i) c

/-- Copy a tree through a temporary pair; the auxiliary register need not be empty. -/
def copy (aux dst src : Fin k) : TreeMachine.Program k Unit := do
  act (.pair dst src aux)
  act (.left dst dst)

theorem exec_copy (aux dst src : Fin k) (c : Cfg k) :
    (copy aux dst src).Exec semantics c 2 () ⟨Function.update c.regs dst (c.regs src)⟩ := by
  have h := (exec_act (.pair dst src aux) c).bind (f := fun _ ↦ act (.left dst dst))
    (exec_act (.left dst dst) (apply (TreeMachine.Action.pair dst src aux) c))
  simpa [copy, Bind.bind, Cfg.apply_def] using h

/-- Compile a program to a machine with the tree operation interpreter and `nop` for the
exits. Each action takes one step. -/
def compile {α : Type} (p : TreeMachine.Program k α) :
    TreeMachine Id k (p.State ⊕ p.Exit) :=
  Program.Syntax.compile eval .nop p

end Program
end Complexity.TreeMachine
