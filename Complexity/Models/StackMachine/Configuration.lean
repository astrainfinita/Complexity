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

export Controller (state observe apply)

/-- One local stack operation; popping an empty stack leaves it empty. -/
inductive Op (Γ : Type*) where
  | nop
  | push (a : Γ)
  | pop
  deriving DecidableEq

/-- Simultaneous local operations, with read-only input and append-only output. -/
structure Action (κ Γ Q : Type*) where
  /-- Move left, stay, or move right within the bounded input. -/
  inputMove : SignType
  /-- Perform one local operation on each work stack. -/
  work : κ → Op Γ
  /-- Append this symbol, or preserve output when absent. -/
  output : Option Γ
  /-- The control state. -/
  state : Q

/-- The top of a stack is the head of its list. Input boundaries observe `none`. -/
@[ext]
structure Cfg (κ Γ Q : Type*) (xs : Array Γ) where
  /-- The control state. -/
  state : Q
  /-- Position shifted by one, with blank boundaries at both ends. -/
  inputPos : Fin (xs.size + 2)
  /-- Work stacks, with their tops at the list heads. -/
  «stacks» : κ → List Γ
  /-- Symbols emitted so far; inaccessible to the controller. -/
  output : Array Γ

variable {κ Γ Q Q' : Type*} {xs : Array Γ}

/-- Execute a local operation on a stack. -/
def Op.apply : Op Γ → List Γ → List Γ
  | .nop, s => s
  | .push a, s => a :: s
  | .pop, s => s.tail

@[simps]
instance : Controller.HasState (Cfg κ Γ Q xs) Q where
  state := Cfg.state

@[simps]
instance : Controller.Observe (Cfg κ Γ Q xs) (Option Γ × (κ → Option Γ)) where
  observe c := (match c.inputPos.val with
    | 0 => none
    | n + 1 => xs[n]?, fun i ↦ (c.stacks i).head?)

@[simps]
instance : Controller.Apply (Cfg κ Γ Q xs) (Action κ Γ Q) where
  apply a c :=
    { state := a.state
      inputPos := Input.movePos c.inputPos a.inputMove
      «stacks» i := (a.work i).apply (c.stacks i)
      output := match a.output with
        | none => c.output
        | some v => c.output.push v }

/-- Relabel the control state without changing storage. -/
@[simps]
def Cfg.mapState (f : Q → Q') (c : Cfg κ Γ Q xs) : Cfg κ Γ Q' xs :=
  { c with state := f c.state }

/-- Relabel an action's destination. -/
@[simps]
def Action.mapState (f : Q → Q') (a : Action κ Γ Q) : Action κ Γ Q' :=
  { a with state := f a.state }

/-- Replace one stack, preserving the control state and external streams. -/
@[simps -fullyApplied]
def Cfg.setStack [DecidableEq κ] (c : Cfg κ Γ Q xs) (i : κ) (w : List Γ) :
    Cfg κ Γ Q xs := { c with «stacks» := Function.update c.stacks i w }

@[simp] theorem Cfg.setStack_self [DecidableEq κ] (c : Cfg κ Γ Q xs) (i : κ) :
    c.setStack i (c.stacks i) = c := by simp [Cfg.setStack]

@[simp] theorem Cfg.setStack_setStack [DecidableEq κ] (c : Cfg κ Γ Q xs) (i : κ)
    (u v : List Γ) : (c.setStack i u).setStack i v = c.setStack i v := by
  simp [Cfg.setStack]

theorem Cfg.setStack_comm [DecidableEq κ] (c : Cfg κ Γ Q xs) {i j : κ} (h : i ≠ j)
    (u v : List Γ) : (c.setStack i u).setStack j v = (c.setStack j v).setStack i u := by
  simp [Cfg.setStack, Function.update_comm h]

end Complexity.StackMachine
