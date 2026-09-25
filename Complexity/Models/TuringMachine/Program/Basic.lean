/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program
public import Complexity.Models.TuringMachine.Basic

/-!
# Programs for multi-tape machines

A program can inspect only the input symbol and the work symbols under the heads.
Every primitive below performs one actual machine transition. Pure results are finite
control labels: returning a value does not write it to the output. `emit` performs output.

The compiler keeps the program's finite internal nodes and exits as its control states.
Neither input data nor the resource information used in proofs is part of this control.
-/

@[expose] public section

namespace Complexity.TM

namespace Program

/-- The local operations recorded by a source program. -/
inductive Op (κ : Type) (Γ : Type) where
  | act (a : Action κ Γ Unit)
  | readInput (s : FinEnum Γ)
  | read (s : FinEnum Γ) (i : κ)
  | observeBits (n : ℕ) (f : (Γ × (κ → Γ)) → Fin n → Bool)

/-- Each operation has a fixed finite shape for its observed result. -/
abbrev Op.Result {κ : Type} {Γ : Type} : Op κ Γ → Type
  | .act _ => Unit
  | .readInput _ | .read _ _ => Γ
  | .observeBits n _ => Vector Bool n

instance {κ : Type} {Γ : Type} (o : Op κ Γ) : Finite o.Result := by
  cases o with
  | act => exact inferInstanceAs (Finite Unit)
  | readInput s | read s _ =>
    let := s
    exact inferInstanceAs (Finite Γ)
  | observeBits n _ =>
    apply Finite.of_injective (fun v : Vector Bool n ↦ fun i : Fin n ↦ v[i])
    intro v w h
    apply Vector.ext
    intro i hi
    exact congrFun h ⟨i, hi⟩

end Program

/-- A monadic finite controller over local multi-tape actions. -/
abbrev Program (κ : Type) (Γ : Type) :=
  Complexity.Program (Γ × (κ → Γ)) (Action κ Γ Unit) (Program.Op κ Γ)
    Program.Op.Result

namespace Program

variable {κ : Type} {Γ α : Type}

/-- A local action which leaves all storage and heads unchanged. -/
def idle : Action κ Γ Unit where
  inputMove := 0
  work := fun _ ↦ (none, 0)
  output := none
  state := ()

/-- An idle action preserves the tape configuration. -/
@[simp]
theorem idle_apply [Inhabited Γ] {xs : Array Γ} (c : Cfg κ Γ Unit xs) :
    apply (idle (κ := κ) (Γ := Γ)) c = c := by
  ext <;> simp [idle, SignType.cast]

/-- The local action used by a single work-head movement. -/
def moveAction [DecidableEq κ] (j : κ) (d : SignType) : Action κ Γ Unit :=
  { idle (κ := κ) with work := fun i ↦ (none, if i = j then d else 0) }

/-- Interpret one recorded operation as one local machine transition. -/
def eval : (o : Op κ Γ) → (Γ × (κ → Γ)) → Action κ Γ Unit × o.Result
  | .act a, _ => (a, ())
  | .readInput _, v => (idle, v.1)
  | .read _ i, v => (idle, v.2 i)
  | .observeBits _ f, v => (idle, Vector.ofFn (f v))

/-- Execute a simultaneous local action in one transition. -/
def act (a : Action κ Γ Unit) : Program κ Γ Unit :=
  Complexity.Program.perform (Op.act a)

/-- Read the current input symbol in one transition. -/
def readInput [FinEnum Γ] : Program κ Γ Γ :=
  Complexity.Program.perform (Op.readInput (κ := κ) (Γ := Γ) inferInstance)

/-- Read the symbol under one work head in one transition. -/
def read [FinEnum Γ] (i : κ) : Program κ Γ Γ :=
  Complexity.Program.perform (Op.read (Γ := Γ) inferInstance i)

/-- Observe a finite collection of Boolean tests in one transition. -/
def observeBits {n : ℕ} (f : (Γ × (κ → Γ)) → Fin n → Bool) :
    Program κ Γ (Vector Bool n) := Complexity.Program.perform (Op.observeBits n f)

/-- Write the current work cell without moving its head. -/
def write [DecidableEq κ] (i : κ) (a : Γ) : Program κ Γ Unit :=
  act { idle (κ := κ) with work := fun j ↦ (if j = i then some a else none, 0) }

/-- Move one work head by at most one cell. -/
def move [DecidableEq κ] (i : κ) (d : SignType) : Program κ Γ Unit :=
  act (moveAction i d)

section Movement

variable [DecidableEq κ]

theorem move_eq_act (j : κ) (d : SignType) :
    move (Γ := Γ) j d = act (moveAction j d) := rfl

variable [Inhabited Γ] {xs : Array Γ}

/-- A move is exactly one local head update; tape data and external streams stay fixed. -/
@[simp] theorem moveAction_apply (j : κ) (d : SignType) (c : Cfg κ Γ Unit xs) :
    apply (moveAction (Γ := Γ) j d) c = c.setWorkPos j (c.workPos j + d.cast) := by
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · rfl
  · funext i
    by_cases h : i = j <;> simp [moveAction, idle, h]
  · rfl

theorem moveAction_setWorkPos (c : Cfg κ Γ Unit xs) (j : κ)
    (p : ℤ) (d : SignType) :
    apply (moveAction (Γ := Γ) j d) (c.setWorkPos j p) = c.setWorkPos j
      (p + d.cast) := by
  simp

end Movement

/-- Move the read-only input head, using the machine's boundary convention. -/
def moveInput (d : SignType) : Program κ Γ Unit :=
  act { idle with inputMove := d }

/-- Append one symbol to the output in one transition. -/
def emit (a : Γ) : Program κ Γ Unit := act { idle with output := some a }

/-- Repeat a body until it returns `true`, charging one dispatch step per iteration. -/
def repeatUntil (p : Program κ Γ Bool) : Program κ Γ Unit :=
  Complexity.Program.repeatUntil idle p

/-- A machine whose finite control is the program graph. All exits halt. -/
def compile (p : Program κ Γ α) : TM Id κ Γ (p.State ⊕ p.Exit) where
  q₀ := (Complexity.Program.compile eval p).start
  halt := Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  transition q v := pure <| match q with
    | .inl q =>
        let (b, q') := (Complexity.Program.compile eval p).next q v
        b.mapState (fun _ ↦ q')
    | .inr e => idle.mapState (fun _ ↦ .inr e)

end Program

end Complexity.TM
