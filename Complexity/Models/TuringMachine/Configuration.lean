/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Basic
public import Complexity.Data.IntMemory.Basic
public import Complexity.Models.Input

/-!
# Configurations and actions of a multi-tape Turing machine

The input is read-only, work tapes use `IntMemory`, and output is appended to an array.
Head positions belong to the machine configuration, independently of the storage interface.
The input head is restricted to the input and one blank cell at each end.

The input/output and action conventions follow CSLib's
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
Absolute work-head positions keep addresses stable under head movement and make local
updates explicit. Blank symbols come from `Inhabited Γ`, independently of the state type.
Local head updates and control-state maps belong to this model layer and preserve unrelated
configuration fields.
-/

@[expose] public section

namespace Complexity.TM

export Controller (state observe apply)

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- One simultaneous transition on an input tape and work tapes indexed by `κ`. -/
structure Action (κ : Type*) (Γ Q : Type*) where
  /-- Input head movement: left, stay, or right. -/
  inputMove : SignType
  /-- An optional write and a movement for each work tape.
  `none` preserves the cell, while `some default` writes a blank. -/
  work : κ → Option Γ × SignType
  /-- An optional symbol to append to the output. -/
  output : Option Γ
  /-- The next state. The machine determines which states are halting. -/
  state : Q

/-- A configuration relative to a fixed, immutable input array. -/
@[ext]
structure Cfg (κ : Type*) (Γ Q : Type*) [Inhabited Γ] (xs : Array Γ) where
  /-- The current state, with no distinguished halting representation. -/
  state : Q
  /-- Input position shifted by one: `0` and `xs.size + 1` are blank boundaries. -/
  inputPos : Fin (xs.size + 2)
  /-- The contents of each work tape. -/
  workTapes : κ → IntMemory Γ
  /-- Absolute positions of the work heads. -/
  workPos : κ → ℤ
  /-- Output already emitted; the transition function cannot read it. -/
  output : Array Γ

namespace Cfg

/-- The symbol at the input head, with `default` for either boundary. -/
def inputSymbol (c : Cfg κ Γ Q xs) : Γ :=
  match c.inputPos.val with
  | 0 => default
  | n + 1 => xs[n]?.getD default

/-- The symbols at the work heads before a transition. -/
def workSymbols (c : Cfg κ Γ Q xs) (i : κ) : Γ :=
  (c.workTapes i)[c.workPos i]

@[simps]
instance : Controller.HasState (Cfg κ Γ Q xs) Q where
  state := Cfg.state

@[simps]
instance : Controller.Observe (Cfg κ Γ Q xs) (Γ × (κ → Γ)) where
  observe c := (c.inputSymbol, c.workSymbols)

end Cfg

/-- Simultaneous local updates for an ordinary configuration. -/
@[simps]
instance : Controller.Apply (Cfg κ Γ Q xs) (Action κ Γ Q) where
  apply a c :=
    { state := a.state
      inputPos := Input.movePos c.inputPos a.inputMove
      workTapes i := match (a.work i).1 with
        | none => c.workTapes i
        | some v => (c.workTapes i).set (c.workPos i) v
      workPos i := c.workPos i + (a.work i).2.cast
      output := match a.output with
        | none => c.output
        | some v => c.output.push v }

theorem Action.getElem_workTapes_apply (a : Action κ Γ Q)
    (c : Cfg κ Γ Q xs) (i : κ) (j : ℤ) :
    ((apply a c).workTapes i)[j] =
      if c.workPos i = j then (a.work i).1.getD (c.workTapes i)[j]
      else (c.workTapes i)[j] := by
  cases h : (a.work i).1 <;> simp [h, IntMemory.getElem_set]

/-- Every work head moves by at most one position. -/
theorem Action.workPos_apply_bounds (a : Action κ Γ Q)
    (c : Cfg κ Γ Q xs) (i : κ) :
    c.workPos i - 1 ≤ (apply a c).workPos i ∧
      (apply a c).workPos i ≤ c.workPos i + 1 := by
  cases h : (a.work i).2 <;> simp [h, SignType.cast]
  omega

theorem Action.output_apply (a : Action κ Γ Q) (c : Cfg κ Γ Q xs) :
    (apply a c).output.toList = c.output.toList ++ a.output.toList := by
  cases h : a.output <;> simp [h]

section LocalUpdates

variable {Q' Q'' : Type*}

section HeadUpdates

variable [DecidableEq κ]

/-- Replace one work-head position while preserving every other configuration field. -/
@[simps -fullyApplied]
def Cfg.setWorkPos (c : Cfg κ Γ Q xs) (i : κ) (p : ℤ) : Cfg κ Γ Q xs :=
  { c with workPos := Function.update c.workPos i p }

@[simp] theorem Cfg.workSymbols_setWorkPos_self (c : Cfg κ Γ Q xs) (i : κ) (p : ℤ) :
    (c.setWorkPos i p).workSymbols i = (c.workTapes i)[p] := by
  simp [workSymbols]

@[simp] theorem Cfg.workSymbols_setWorkPos_of_ne (c : Cfg κ Γ Q xs) {i j : κ}
    (h : j ≠ i) (p : ℤ) : (c.setWorkPos i p).workSymbols j = c.workSymbols j := by
  simp [workSymbols, h]

@[simp] theorem Cfg.setWorkPos_self (c : Cfg κ Γ Q xs) (i : κ) :
    c.setWorkPos i (c.workPos i) = c := by
  simp [setWorkPos]

@[simp] theorem Cfg.setWorkPos_setWorkPos (c : Cfg κ Γ Q xs) (i : κ) (p q : ℤ) :
    (c.setWorkPos i p).setWorkPos i q = c.setWorkPos i q := by
  simp [setWorkPos]

/-- Updates to distinct heads commute. -/
theorem Cfg.setWorkPos_comm (c : Cfg κ Γ Q xs) {i j : κ} (h : i ≠ j) (p q : ℤ) :
    (c.setWorkPos i p).setWorkPos j q = (c.setWorkPos j q).setWorkPos i p := by
  simp only [setWorkPos, Function.update_comm h]

end HeadUpdates

/-- Relabel a configuration's control state. -/
@[simps -fullyApplied]
def Cfg.mapState (f : Q → Q') (c : Cfg κ Γ Q xs) : Cfg κ Γ Q' xs :=
  { c with state := f c.state }

@[simp]
theorem Cfg.inputSymbol_mapState (f : Q → Q') (c : Cfg κ Γ Q xs) :
    (c.mapState f).inputSymbol = c.inputSymbol := rfl

@[simp]
theorem Cfg.workSymbols_mapState (f : Q → Q') (c : Cfg κ Γ Q xs) :
    (c.mapState f).workSymbols = c.workSymbols := rfl

@[simp]
theorem Cfg.mapState_id (c : Cfg κ Γ Q xs) : c.mapState id = c := rfl

@[simp]
theorem Cfg.mapState_mapState (f : Q → Q') (g : Q' → Q'') (c : Cfg κ Γ Q xs) :
    (c.mapState f).mapState g = c.mapState (g ∘ f) := rfl

@[simp] theorem Cfg.mapState_setWorkPos [DecidableEq κ] (f : Q → Q') (c : Cfg κ Γ Q xs)
    (i : κ) (p : ℤ) :
    (c.setWorkPos i p).mapState f = (c.mapState f).setWorkPos i p := rfl

/-- Relabel the destination of an action. -/
@[simps -fullyApplied]
def Action.mapState (f : Q → Q') (a : Action κ Γ Q) : Action κ Γ Q' :=
  { a with state := f a.state }

section ActionMaps

omit [Inhabited Γ]

@[simp]
theorem Action.mapState_id (a : Action κ Γ Q) : a.mapState id = a := rfl

@[simp]
theorem Action.mapState_mapState (f : Q → Q') (g : Q' → Q'')
    (a : Action κ Γ Q) :
    (a.mapState f).mapState g = a.mapState (g ∘ f) := rfl

end ActionMaps

/-- Relabeling commutes with executing an action. -/
@[simp]
theorem Action.apply_mapState (f : Q → Q') (a : Action κ Γ Q)
    (c : Cfg κ Γ Q xs) :
    apply (a.mapState f) (c.mapState f) = (apply a c).mapState f := rfl

end LocalUpdates

end Complexity.TM
