/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Basic
public import Complexity.Data.Tree.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Local actions and configurations of a tree register machine

Each action selects one instruction. `nop` leaves every register unchanged; every other
instruction has its destination as its first index. Operands are read from the old register
bank. Control sees only root shapes. A transition selects the next control state together with
one instruction.
-/

@[expose] public section

namespace Complexity.TreeMachine

export Controller (observe apply)

/-- A register instruction; its first index is the destination, followed by its sources. -/
inductive Action (k : ℕ) where
  | nop
  | left (i j : Fin k)
  | right (i j : Fin k)
  | pair (i j l : Fin k)
  deriving Inhabited, DecidableEq, Repr

variable {k l : ℕ}

/-- The selected destination, absent for `nop`. -/
def Action.dst : Action k → Option (Fin k)
  | .nop => none
  | .left i _ => some i
  | .right i _ => some i
  | .pair i _ _ => some i

@[simp] theorem Action.dst_nop : (Action.nop : Action k).dst = none := rfl

@[simp] theorem Action.dst_left (i j : Fin k) : (Action.left i j).dst = some i := rfl

@[simp] theorem Action.dst_right (i j : Fin k) : (Action.right i j).dst = some i := rfl

@[simp] theorem Action.dst_pair (i j l : Fin k) : (Action.pair i j l).dst = some i := rfl

/-- Execute one instruction on the register bank, reading sources before the update. -/
def Action.eval (ρ : Fin k → Tree) : Action k → (Fin k → Tree)
  | .nop => ρ
  | .left i j => Function.update ρ i (ρ j).left
  | .right i j => Function.update ρ i (ρ j).right
  | .pair i j l => Function.update ρ i (Tree.pair (ρ j) (ρ l))

@[simp] theorem Action.eval_nop (ρ : Fin k → Tree) : Action.nop.eval ρ = ρ := rfl

@[simp] theorem Action.eval_left (ρ : Fin k → Tree) (i j : Fin k) :
    (Action.left i j).eval ρ = Function.update ρ i (ρ j).left := rfl

@[simp] theorem Action.eval_right (ρ : Fin k → Tree) (i j : Fin k) :
    (Action.right i j).eval ρ = Function.update ρ i (ρ j).right := rfl

@[simp] theorem Action.eval_pair (ρ : Fin k → Tree) (i j l : Fin k) :
    (Action.pair i j l).eval ρ = Function.update ρ i (Tree.pair (ρ j) (ρ l)) := rfl

/-- An instruction leaves every unselected register unchanged. -/
theorem Action.eval_of_dst_ne (ρ : Fin k → Tree) (o : Action k) (i : Fin k)
    (h : o.dst ≠ some i) : o.eval ρ i = ρ i := by
  cases o <;> simp_all [dst, eval, eq_comm]

/-- Rename every register index, including the destination. -/
def Action.rename (f : Fin k → Fin l) : Action k → Action l
  | .nop => .nop
  | .left i j => .left (f i) (f j)
  | .right i j => .right (f i) (f j)
  | .pair i j l => .pair (f i) (f j) (f l)

@[simp] theorem Action.dst_rename (f : Fin k → Fin l) (o : Action k) :
    (o.rename f).dst = o.dst.map f := by
  cases o <;> rfl

/-- Injective renaming preserves the bank semantics on the renamed registers. -/
theorem Action.eval_rename (f : Fin k → Fin l) (hf : Function.Injective f)
    (ρ : Fin l → Tree) (o : Action k) :
    (o.rename f).eval ρ ∘ f = o.eval (ρ ∘ f) := by
  funext i
  cases o <;> simp [rename, eval, Function.comp_def, Function.update_apply, hf.eq_iff]

/-- The register bank of a tree machine. A machine configuration pairs it with a control
state. -/
@[ext] structure Cfg (k : ℕ) where
  /-- Current register values. -/
  regs : Fin k → Tree
  deriving Inhabited

namespace Cfg

/-- The finite vector of observations passed to the transition function. -/
@[simps]
instance : Controller.Observe (Cfg k) (Fin k → Bool) where
  observe c i := Tree.root (c.regs i)

/-- Apply one instruction. `nop` is not skipped. The generated `Cfg.apply_def` is not a simp lemma:
simp keeps `apply o c` and works through `(apply o c).regs`. -/
@[simps -fullyApplied, simps -isSimp apply]
instance : Controller.Apply (Cfg k) (Action k) where
  apply o c := ⟨o.eval c.regs⟩

end Cfg

/-- Put the input tree in one register, leaving all other registers empty. -/
def input (i : Fin k) (a : Tree) : Fin k → Tree :=
  Function.update (fun _ => Tree.nil) i a

@[simp] theorem input_get (i : Fin k) (a : Tree) : input i a i = a := by
  simp [input]

@[simp] theorem input_get_of_ne {i j : Fin k} (a : Tree) (h : j ≠ i) :
    input i a j = Tree.nil := by
  simp [input, h]

/-- Along an injective map of register indices, the input in register `e i` reads as the input in
register `i`. -/
theorem input_comp {e : Fin k → Fin l} (he : e.Injective) (i : Fin k) (a : Tree) :
    input (e i) a ∘ e = input i a :=
  Function.update_comp_eq_of_injective _ he i a

/-- Registers other than the selected destination retain their values. -/
theorem Action.regs_apply_of_ne (o : Action k) (c : Cfg k) {i : Fin k} (h : o.dst ≠ some i) :
    (apply o c).regs i = c.regs i :=
  o.eval_of_dst_ne c.regs i h

@[simp] theorem Action.apply_nop (c : Cfg k) : apply (Action.nop : Action k) c = c := rfl

end Complexity.TreeMachine
