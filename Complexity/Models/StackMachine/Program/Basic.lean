/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Basic
public import Complexity.Control.Program.Loop
public import Complexity.Control.Program.Compiler

/-! # Finite programs over local stack operations -/

@[expose] public section

namespace Complexity.StackMachine

namespace Program

/-- Primitive actions and finite observations for stack programs. -/
inductive Op (κ Γ : Type) where
  | act (a : Action κ Γ)
  | readInput (s : FinEnum (Option Γ))
  | read (s : FinEnum (Option Γ)) (i : κ)
  | observeBits (n : ℕ) (f : (Option Γ × (κ → Option Γ)) → Fin n → Bool)

/-- The finite result returned by a primitive instruction. -/
abbrev Op.Result {κ Γ : Type} : Op κ Γ → Type
  | .act _ => Unit
  | .readInput _ | .read _ _ => Option Γ
  | .observeBits n _ => Vector Bool n

instance {κ Γ : Type} (o : Op κ Γ) : Finite o.Result := by
  cases o with
  | act => exact inferInstanceAs (Finite Unit)
  | readInput s | read s _ =>
    let := s
    exact inferInstanceAs (Finite (Option Γ))
  | observeBits n _ =>
    apply Finite.of_injective (fun v : Vector Bool n ↦ fun i : Fin n ↦ v[i])
    intro v w h
    apply Vector.ext
    intro i hi
    exact congrFun h ⟨i, hi⟩

end Program

/-- Each observed result is finite; unbounded stacks stay in the semantic configuration. -/
protected abbrev Program (κ Γ : Type) :=
  Program (Option Γ × (κ → Option Γ)) (Action κ Γ) (Program.Op κ Γ)
    Program.Op.Result

namespace Program

variable {κ Γ : Type}

/-- A control-only action still consumes one transition. -/
def idle : Action κ Γ where
  inputMove := 0
  work := fun _ ↦ .nop
  output := none

@[simp] theorem idle_apply {xs : Array Γ} (c : Cfg κ Γ xs) :
    apply (idle (κ := κ) (Γ := Γ)) c = c := by
  apply Cfg.ext <;> simp [idle, funext_iff, StackMachine.Op.apply]

/-- Interpret an instruction as a local action and its observed result. -/
def eval : (o : Op κ Γ) → (Option Γ × (κ → Option Γ)) → Action κ Γ × o.Result
  | .act a, _ => (a, ())
  | .readInput _, v => (idle, v.1)
  | .read _ i, v => (idle, v.2 i)
  | .observeBits _ f, v => (idle, Vector.ofFn (f v))

/-- Execute one simultaneous local action. -/
def act (a : Action κ Γ) : StackMachine.Program κ Γ Unit :=
  Program.perform (Op.act a)

/-- Read the input symbol, or `none` at either boundary. -/
def readInput [FinEnum Γ] : StackMachine.Program κ Γ (Option Γ) :=
  Program.perform (Op.readInput inferInstance)

/-- Read one stack top, or `none` for an empty stack. -/
def read [FinEnum Γ] (i : κ) : StackMachine.Program κ Γ (Option Γ) :=
  Program.perform (Op.read inferInstance i)

/-- Observe finitely many Boolean tests in one transition. -/
def observeBits {n : ℕ} (f : (Option Γ × (κ → Option Γ)) → Fin n → Bool) :
    StackMachine.Program κ Γ (Vector Bool n) := Program.perform (Op.observeBits n f)

/-- Push one symbol onto a selected stack. -/
def push [DecidableEq κ] (i : κ) (a : Γ) : StackMachine.Program κ Γ Unit :=
  act { idle (κ := κ) with work := fun j ↦ if j = i then .push a else .nop }

/-- Pop one selected stack, leaving it empty if it already was. -/
def pop [DecidableEq κ] (i : κ) : StackMachine.Program κ Γ Unit :=
  act { idle (κ := κ) with work := fun j ↦ if j = i then .pop else .nop }

/-- Move the input head using the bounded input convention. -/
def moveInput (d : SignType) : StackMachine.Program κ Γ Unit :=
  act { idle with inputMove := d }

/-- Append one symbol to the external output. -/
def emit (a : Γ) : StackMachine.Program κ Γ Unit := act { idle with output := some a }

/-- Loop dispatch uses a no-op, which costs one transition per iteration. -/
def repeatUntil (p : StackMachine.Program κ Γ Bool) : StackMachine.Program κ Γ Unit :=
  Program.repeatUntilWith idle p

/-- Interpret instructions directly on complete stack configurations. -/
@[simps eval observe act]
def semantics (xs : Array Γ) :
    Program.Semantics (Option Γ × (κ → Option Γ)) (Action κ Γ) (Op κ Γ) Op.Result
      (Cfg κ Γ xs) where
  eval := eval
  observe := Controller.observe
  act := apply

open Std.WP

@[spec] theorem spec_act (a : Action κ Γ) (xs : Array Γ)
    (s : Cfg κ Γ xs) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((act a).verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = () ∧ t = apply a s ∧ c = b - 1) x :=
  Program.spec_perform (Op.act a) (semantics xs) s b h x

@[spec] theorem spec_readInput [FinEnum Γ] (xs : Array Γ)
    (s : Cfg κ Γ xs) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple (readInput.verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = (observe s : Option Γ × (κ → Option Γ)).1 ∧ t = s ∧ c = b - 1) x := by
  simpa [readInput, eval] using
    Program.spec_perform (Op.readInput inferInstance) (semantics xs) s b h x

@[spec] theorem spec_read [FinEnum Γ] (i : κ) (xs : Array Γ)
    (s : Cfg κ Γ xs) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((read i).verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = (s.stacks i).head? ∧ t = s ∧ c = b - 1) x := by
  simpa [read, eval] using
    Program.spec_perform (Op.read inferInstance i) (semantics xs) s b h x

@[spec] theorem spec_observeBits {n : ℕ} (f : (Option Γ × (κ → Option Γ)) → Fin n → Bool)
    (xs : Array Γ) (s : Cfg κ Γ xs) (b : ℕ) (h : 0 < b) (x : Unit) :
    Triple ((observeBits f).verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun v t c ↦ v = Vector.ofFn (f (observe s)) ∧ t = s ∧ c = b - 1) x := by
  simpa [observeBits, eval] using
    Program.spec_perform (Op.observeBits n f) (semantics xs) s b h x

@[simp] theorem pushAction_apply [DecidableEq κ] {xs : Array Γ}
    (c : Cfg κ Γ xs) (i : κ) (a : Γ) :
    apply { idle (κ := κ) with work := fun j ↦ if j = i then .push a else .nop } c =
      c.setStack i (a :: c.stacks i) := by
  ext j <;> simp [idle, Function.update_apply]
  split_ifs <;> simp_all [StackMachine.Op.apply]

@[simp] theorem popAction_apply [DecidableEq κ] {xs : Array Γ}
    (c : Cfg κ Γ xs) (i : κ) :
    apply { idle (κ := κ) (Γ := Γ) with work := fun j ↦ if j = i then .pop else .nop } c =
      c.setStack i (c.stacks i).tail := by
  ext j <;> simp [idle, Function.update_apply]
  split_ifs <;> simp_all [StackMachine.Op.apply]

@[spec] theorem verify_push [DecidableEq κ] (i : κ) (a : Γ) (xs : Array Γ) :
    (push i a).verify (semantics xs) =
      (act { idle (κ := κ) with work := fun j ↦ if j = i then .push a else .nop }).verify
        (semantics xs) := rfl

@[spec] theorem verify_pop [DecidableEq κ] (i : κ) (xs : Array Γ) :
    (pop i).verify (semantics xs) =
      (act { idle (κ := κ) with work := fun j ↦ if j = i then .pop else .nop }).verify
        (semantics xs) := rfl

/-- Compile a stack program to a native machine with the stack operation interpreter and
`idle` for the exits, with one transition per local action. -/
def compile {α : Type} (p : StackMachine.Program κ Γ α) :
    StackMachine Id κ Γ (p.State ⊕ p.Exit) :=
  Program.Syntax.compile eval idle p

end Program
end Complexity.StackMachine
