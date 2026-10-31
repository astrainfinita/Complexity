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

/-- Interpret a program directly on register values, without machine control states. -/
@[simps eval observe act]
def semantics :
    Program.Semantics (Fin k → Bool) (TreeMachine.Action k) (Op k) Op.Result (Fin k → Tree) where
  eval := eval
  observe ρ i := (ρ i).root
  act o ρ := o.eval ρ

theorem exec_act (o : TreeMachine.Action k) (ρ : Fin k → Tree) :
    (act o).Exec semantics ρ 1 () (o.eval ρ) :=
  Program.Exec.perform semantics (.act o) ρ

theorem exec_root (i : Fin k) (ρ : Fin k → Tree) :
    (root i).Exec semantics ρ 1 (ρ i).root ρ :=
  Program.Exec.perform semantics (.root i) ρ

/-- Copy a tree through a temporary pair; the auxiliary register need not be empty. -/
def copy (aux dst src : Fin k) : TreeMachine.Program k Unit := do
  act (.pair dst src aux)
  act (.left dst dst)

theorem exec_copy (aux dst src : Fin k) (ρ : Fin k → Tree) :
    (copy aux dst src).Exec semantics ρ 2 () (Function.update ρ dst (ρ src)) := by
  have h := (exec_act (.pair dst src aux) ρ).bind (f := fun _ ↦ act (.left dst dst))
    (exec_act (.left dst dst) ((TreeMachine.Action.pair dst src aux).eval ρ))
  simpa [copy, Bind.bind] using h

/-- Exits of the generic control graph become halting states. Each action takes one step. -/
def compile {α : Type} (p : TreeMachine.Program k α) :
    TreeMachine Id k (p.State ⊕ p.Exit) where
  q₀ := (p.toControl eval).start
  halt := Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  transition q v := pure <| match q with
    | .inl q =>
        let (o, q') := (p.toControl eval).next q v
        (q', o)
    | .inr e => (.inr e, .nop)

end Program
end Complexity.TreeMachine
