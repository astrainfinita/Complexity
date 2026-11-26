/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Basic
public import Complexity.Models.Input

/-! # Configurations and actions of a multiple-stack machine -/

@[expose] public section

namespace Complexity.StackMachine

export Controller (observe apply)

/-- One local stack operation; popping an empty stack leaves it empty. -/
inductive Op (Γ : Type*) where
  | nop
  | push (a : Γ)
  | pop
  deriving DecidableEq

/-- Simultaneous local operations, with read-only input and append-only output. -/
structure Action (κ Γ : Type*) where
  /-- Move left, stay, or move right within the bounded input. -/
  inputMove : SignType
  /-- Perform one local operation on each work stack. -/
  work : κ → Op Γ
  /-- Append this symbol, or preserve output when absent. -/
  output : Option Γ

/-- The top of a stack is the head of its list. Input boundaries observe `none`. The control
state is kept apart from this storage. -/
@[ext]
structure Cfg (κ Γ : Type*) (xs : Array Γ) where
  /-- Position shifted by one, with blank boundaries at both ends. -/
  inputPos : Fin (xs.size + 2)
  /-- Work stacks, with their tops at the list heads. -/
  «stacks» : κ → List Γ
  /-- Symbols emitted so far; inaccessible to the controller. -/
  output : Array Γ

variable {κ Γ : Type*} {xs : Array Γ}

/-- Execute a local operation on a stack. -/
def Op.apply : Op Γ → List Γ → List Γ
  | .nop, s => s
  | .push a, s => a :: s
  | .pop, s => s.tail

/-- An operation grows a stack by at most one symbol. -/
theorem Op.length_apply_le (o : Op Γ) (s : List Γ) : (o.apply s).length ≤ s.length + 1 := by
  cases o <;> simp [Op.apply]
  omega

@[simps]
instance : Controller.Observe (Cfg κ Γ xs) (Option Γ × (κ → Option Γ)) where
  observe c := (Input.read xs c.inputPos.val, fun i ↦ (c.stacks i).head?)

@[simps]
instance : Controller.Apply (Cfg κ Γ xs) (Action κ Γ) where
  apply a c :=
    { inputPos := Input.movePos c.inputPos a.inputMove
      «stacks» i := (a.work i).apply (c.stacks i)
      output := match a.output with
        | none => c.output
        | some v => c.output.push v }

/-- The action leaving a configuration unchanged; it still consumes one transition. -/
def Action.idle : Action κ Γ where
  inputMove := 0
  work _ := .nop
  output := none

@[simp] theorem apply_idle (c : Cfg κ Γ xs) : apply (Action.idle : Action κ Γ) c = c := by
  apply Cfg.ext <;> simp [Action.idle, funext_iff, Op.apply]

/-- Replace one stack, preserving the input head and the output. -/
@[simps -fullyApplied]
def Cfg.setStack [DecidableEq κ] (c : Cfg κ Γ xs) (i : κ) (w : List Γ) :
    Cfg κ Γ xs := { c with «stacks» := Function.update c.stacks i w }

@[simp] theorem Cfg.setStack_self [DecidableEq κ] (c : Cfg κ Γ xs) (i : κ) :
    c.setStack i (c.stacks i) = c := by simp [Cfg.setStack]

@[simp] theorem Cfg.setStack_setStack [DecidableEq κ] (c : Cfg κ Γ xs) (i : κ)
    (u v : List Γ) : (c.setStack i u).setStack i v = c.setStack i v := by
  simp [Cfg.setStack]

theorem Cfg.setStack_comm [DecidableEq κ] (c : Cfg κ Γ xs) {i j : κ} (h : i ≠ j)
    (u v : List Γ) : (c.setStack i u).setStack j v = (c.setStack j v).setStack i u := by
  simp [Cfg.setStack, Function.update_comm h]

end Complexity.StackMachine
