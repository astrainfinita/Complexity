/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Basic
public import Complexity.Models.TreeMachine.Simulation.Representation
public import Complexity.Control.Program.Loop
public import Complexity.Control.Program.For
public import Mathlib.Basic.Finite.Prod
public import Complexity.Models.TreeMachine.Program.Pair
public import Complexity.Models.TreeMachine.Program.Project
public import Complexity.Models.TuringMachine.Program.Word.Clear
public import Complexity.Models.TuringMachine.Program.Word.IO

/-!
# A tree simulator written as a compositional program

Data tapes store contiguous bits from address zero. Only the counter tape has a fixed
nonblank origin. Control flow uses sequencing, finite-value loops, and verified tape routines.
The register loops are unrolled at construction time; only the source control state and
the bank flag are carried around the runtime simulation loop.

The external input is one tree; all other registers begin as nil. Component specifications
compose into the complete time-and-space refinement theorem in `Program.Correctness`.
-/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.Program

open TM.Program.Word TreeMachine.Program

variable {n k : ℕ} {Q : Type}

/-- Read all register roots without exposing their unbounded contents. -/
def roots (b : Bool) : TM.Program (Fin (2 * k + 1)) (Option Bool) (Fin k → Bool) := do
  let v ← TM.Program.observeBits fun v i ↦ v.2 (Compiler.data b i) == some true
  pure (fun i ↦ v[i])

/-- Fill an empty destination word from the unchanged source register bank. -/
def make (b : Bool) (a : Action k Q) (i : Fin k) :
    TM.Program (Fin (2 * k + 1)) (Option Bool) Unit := do
  let d := Compiler.data (!b) i
  match a.writeAt i with
  | none | some .nop =>
      append d (Compiler.data b i)
      rewind d
  | some (.left _ j) => project d (Compiler.data b j) (Compiler.counter k) false
  | some (.right _ j) => project d (Compiler.data b j) (Compiler.counter k) true
  | some (.pair _ j l) => pair d (Compiler.data b j) (Compiler.data b l)

/-- Clear one destination word, then construct the selected source result there. -/
def build (b : Bool) (a : Action k Q) (i : Fin k) :
    TM.Program (Fin (2 * k + 1)) (Option Bool) Unit := do
  clear (Compiler.data (!b) i)
  make b a i

/-- One source transition, or output production once the source has halted. -/
def body (M : TreeMachine Id k Q) (o : Fin k) (s : Q × Bool) :
    TM.Program (Fin (2 * k + 1)) (Option Bool) ((Q × Bool) ⊕ Unit) := do
  if M.halt s.1 then
    emit (Compiler.data s.2 o)
    pure (.inr ())
  else
    let v ← roots s.2
    let a := (M.transition s.1 v).run
    Complexity.Program.forFin (build s.2 a)
    pure (.inl (a.state, !s.2))

/-- Mark the counter and initialize every non-input source register to `nil`. -/
def boot (i : Fin k) : TM.Action (Fin (2 * k + 1)) (Option Bool) Unit :=
  { TM.Program.idle (κ := Fin (2 * k + 1)) with
    work := fun j ↦
      (if j = Compiler.counter k then some (some true)
       else if j.val < k ∧ j ≠ Compiler.data false i then some (some false) else none, 0) }

/-- Load the unique external tree into its designated register. -/
def init (i : Fin k) : TM.Program (Fin (2 * k + 1)) (Option Bool) Unit := do
  TM.Program.act (boot i)
  load (Compiler.data false i)

/-- The entire tree simulator, with no manually maintained phase or continuation type. -/
def program [FinEnum Q] (M : TreeMachine Id k Q) (i o : Fin k) :
    TM.Program (Fin (2 * k + 1)) (Option Bool) Unit := do
  init i
  Complexity.Program.loopOn TM.Program.idle (body M o) (M.q₀, false)

end Complexity.TreeMachine.Simulation.Program

namespace Complexity.TreeMachine.Simulation

/-- Compile the monadic tree simulator to an ordinary finite multi-tape controller. -/
def compiler {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q] (M : TreeMachine Id k Q) :=
  TM.Program.compile (Program.program M 0 0)

end Complexity.TreeMachine.Simulation
