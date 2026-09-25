/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller
public import Complexity.Data.Tree
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Local actions and configurations of a tree register machine

Each action selects one instruction. `nop` leaves every register unchanged; every other
instruction has its destination as its first index. Operands are read from the old register
bank. Control sees only root shapes.
-/

@[expose] public section

namespace Complexity.TreeMachine

export Controller (state observe apply)

/-- A register instruction; its first index is the destination, followed by its sources. -/
inductive Op (k : ℕ) where
  | nop
  | left (i j : Fin k)
  | right (i j : Fin k)
  | pair (i j l : Fin k)
  deriving Inhabited, DecidableEq, Repr

variable {k l : ℕ} {Q : Type*}

/-- The selected destination, absent for `nop`. -/
def Op.dst : Op k → Option (Fin k)
  | .nop => none
  | .left i _ => some i
  | .right i _ => some i
  | .pair i _ _ => some i

@[simp] theorem Op.dst_nop : (Op.nop : Op k).dst = none := rfl

@[simp] theorem Op.dst_left (i j : Fin k) : (Op.left i j).dst = some i := rfl

@[simp] theorem Op.dst_right (i j : Fin k) : (Op.right i j).dst = some i := rfl

@[simp] theorem Op.dst_pair (i j l : Fin k) : (Op.pair i j l).dst = some i := rfl

/-- Execute one instruction on the register bank, reading sources before the update. -/
def Op.eval (ρ : Fin k → Tree) : Op k → (Fin k → Tree)
  | .nop => ρ
  | .left i j => Function.update ρ i (ρ j).left
  | .right i j => Function.update ρ i (ρ j).right
  | .pair i j l => Function.update ρ i (Tree.pair (ρ j) (ρ l))

@[simp] theorem Op.eval_nop (ρ : Fin k → Tree) : Op.nop.eval ρ = ρ := rfl

@[simp] theorem Op.eval_left (ρ : Fin k → Tree) (i j : Fin k) :
    (Op.left i j).eval ρ = Function.update ρ i (ρ j).left := rfl

@[simp] theorem Op.eval_right (ρ : Fin k → Tree) (i j : Fin k) :
    (Op.right i j).eval ρ = Function.update ρ i (ρ j).right := rfl

@[simp] theorem Op.eval_pair (ρ : Fin k → Tree) (i j l : Fin k) :
    (Op.pair i j l).eval ρ = Function.update ρ i (Tree.pair (ρ j) (ρ l)) := rfl

/-- An instruction leaves every unselected register unchanged. -/
theorem Op.eval_of_dst_ne (ρ : Fin k → Tree) (o : Op k) (i : Fin k)
    (h : o.dst ≠ some i) : o.eval ρ i = ρ i := by
  cases o <;> simp_all [dst, eval, eq_comm]

/-- Rename every register index, including the destination. -/
def Op.rename (f : Fin k → Fin l) : Op k → Op l
  | .nop => .nop
  | .left i j => .left (f i) (f j)
  | .right i j => .right (f i) (f j)
  | .pair i j l => .pair (f i) (f j) (f l)

@[simp] theorem Op.dst_rename (f : Fin k → Fin l) (o : Op k) :
    (o.rename f).dst = o.dst.map f := by
  cases o <;> rfl

/-- Injective renaming preserves the bank semantics on the renamed registers. -/
theorem Op.eval_rename (f : Fin k → Fin l) (hf : Function.Injective f)
    (ρ : Fin l → Tree) (o : Op k) :
    (o.rename f).eval ρ ∘ f = o.eval (ρ ∘ f) := by
  funext i
  cases o <;> simp [rename, eval, Function.comp_def, Function.update_apply, hf.eq_iff]

/-- One register instruction and its next control state. -/
@[ext] structure Action (k : ℕ) (Q : Type*) where
  /-- The instruction to execute, including an explicit `nop`. -/
  op : Op k
  /-- State after applying the action. -/
  state : Q

/-- View the selected update at one register; this does not add independent write choices. -/
def Action.writeAt (a : Action k Q) (i : Fin k) : Option (Op k) :=
  match a.op.dst with
  | none => none
  | some j => if i = j then some a.op else none

@[simp] theorem Action.writeAt_of_nop (a : Action k Q) (i : Fin k)
    (h : a.op = .nop) : a.writeAt i = none := by
  simp [writeAt, h]

theorem Action.writeAt_of_dst (a : Action k Q) {i : Fin k}
    (h : a.op.dst = some i) (j : Fin k) :
    a.writeAt j = if j = i then some a.op else none := by
  simp [writeAt, h]

theorem Action.writeAt_eq_some_iff (a : Action k Q) {i : Fin k} {o : Op k} :
    a.writeAt i = some o ↔ a.op = o ∧ o.dst = some i := by
  unfold writeAt
  cases hd : a.op.dst with
  | none =>
      constructor
      · simp
      · rintro ⟨ho, hi⟩
        rw [ho, hi] at hd
        contradiction
  | some j =>
      by_cases hi : i = j
      · subst i
        simp only [ite_true, Option.some.injEq]
        exact ⟨fun h ↦ ⟨h, h ▸ hd⟩, And.left⟩
      · simp only [hi, ite_false]
        constructor
        · simp
        · rintro ⟨rfl, ho⟩
          rw [ho] at hd
          exact (hi (Option.some.inj hd)).elim

theorem Action.writeAt_dst (a : Action k Q) {i : Fin k} {o : Op k}
    (h : a.writeAt i = some o) : o.dst = some i :=
  (a.writeAt_eq_some_iff.mp h).2

theorem Action.writeAt_ne_nop (a : Action k Q) (i : Fin k) : a.writeAt i ≠ some .nop := by
  intro h
  have := a.writeAt_dst h
  contradiction

/-- A plain control state and a fixed bank of tree values. -/
@[ext] structure Cfg (k : ℕ) (Q : Type*) where
  /-- Current control state. -/
  state : Q
  /-- Current register values. -/
  regs : Fin k → Tree
  deriving Inhabited

@[simps]
instance Cfg.instHasState : Controller.HasState (Cfg k Q) Q where
  state := Cfg.state

/-- The finite vector of observations passed to the transition function. -/
@[simps]
instance Cfg.instObserve : Controller.Observe (Cfg k Q) (Fin k → Bool) where
  observe c i := Tree.root (c.regs i)

/-- Apply one instruction, including its next state. `nop` is not skipped. -/
@[simps -fullyApplied]
instance : Controller.Apply (Cfg k Q) (Action k Q) where
  apply a c := ⟨a.state, a.op.eval c.regs⟩

/-- Put the input tree in one register, leaving all other registers empty. -/
def input (i : Fin k) (a : Tree) : Fin k → Tree :=
  Function.update (fun _ => Tree.nil) i a

@[simp] theorem input_get (i : Fin k) (a : Tree) : input i a i = a := by
  simp [input]

@[simp] theorem input_get_of_ne {i j : Fin k} (a : Tree) (h : j ≠ i) :
    input i a j = Tree.nil := by
  simp [input, h]

theorem Action.regs_apply (a : Action k Q) (c : Cfg k Q) (i : Fin k) :
    (apply a c).regs i = ((a.writeAt i).map (fun o ↦ o.eval c.regs i)).getD (c.regs i) := by
  cases h : a.op with
  | nop => simp [writeAt, h]
  | left j l | right j l | pair j l m =>
      by_cases hi : i = j <;> simp [writeAt, h, hi]

@[simp] theorem Action.regs_apply_of_none (a : Action k Q) (c : Cfg k Q)
    {i : Fin k} (h : a.writeAt i = none) : (apply a c).regs i = c.regs i := by
  rw [regs_apply, h]
  rfl

@[simp] theorem Action.regs_apply_of_some (a : Action k Q) (c : Cfg k Q)
    {i : Fin k} {o : Op k} (h : a.writeAt i = some o) :
    (apply a c).regs i = o.eval c.regs i := by
  rw [regs_apply, h]
  rfl

/-- Executing `nop` changes only the control state. -/
@[simp] theorem Action.apply_of_nop (a : Action k Q) (c : Cfg k Q)
    (h : a.op = .nop) : apply a c = { c with state := a.state } := by
  ext <;> simp [h]

/-- A left projection changes exactly its destination, using the old operand. -/
theorem Action.apply_of_left (a : Action k Q) (c : Cfg k Q)
    {i j : Fin k} (h : a.op = .left i j) :
    apply a c =
      { c with state := a.state, regs := Function.update c.regs i (c.regs j).left } := by
  ext <;> simp [h]

/-- A right projection changes exactly its destination, using the old operand. -/
theorem Action.apply_of_right (a : Action k Q) (c : Cfg k Q)
    {i j : Fin k} (h : a.op = .right i j) :
    apply a c =
      { c with state := a.state, regs := Function.update c.regs i (c.regs j).right } := by
  ext <;> simp [h]

/-- Pairing reads both sources before writing its destination. -/
theorem Action.apply_of_pair (a : Action k Q) (c : Cfg k Q)
    {i j l : Fin k} (h : a.op = .pair i j l) :
    apply a c = { c with
      state := a.state, regs := Function.update c.regs i (Tree.pair (c.regs j) (c.regs l)) } := by
  ext <;> simp [h]

/-- Registers other than the selected destination retain their values. -/
theorem Action.regs_apply_of_ne (a : Action k Q) (c : Cfg k Q)
    {i : Fin k} (h : a.op.dst ≠ some i) : (apply a c).regs i = c.regs i :=
  a.op.eval_of_dst_ne c.regs i h

/-- Change control while keeping every register. -/
def Action.keep (q : Q) : Action k Q := ⟨.nop, q⟩

@[simp] theorem Action.writeAt_keep (q : Q) (i : Fin k) : (Action.keep q).writeAt i = none := rfl

@[simp] theorem Action.apply_keep (q : Q) (c : Cfg k Q) :
    apply (Action.keep (k := k) q) c = { c with state := q } := rfl

/-- Execute an instruction and enter the given control state. -/
def Action.assign (q : Q) (o : Op k) : Action k Q := ⟨o, q⟩

@[simp] theorem Action.writeAt_assign (q : Q) (o : Op k) (j : Fin k) :
    (Action.assign q o).writeAt j =
      match o.dst with | none => none | some i => if j = i then some o else none := rfl

theorem Action.regs_assign (q : Q) (o : Op k) (c : Cfg k Q) :
    (apply (Action.assign q o) c).regs = o.eval c.regs := rfl

@[simp] theorem Action.apply_assign (q : Q) (o : Op k) (c : Cfg k Q) :
    apply (Action.assign q o) c = ⟨q, o.eval c.regs⟩ := rfl

end Complexity.TreeMachine
