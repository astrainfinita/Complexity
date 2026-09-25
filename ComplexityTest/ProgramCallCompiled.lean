/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Call
import Complexity.Models.TuringMachine.Program.Word.Configuration
import Complexity.Models.TuringMachine.RedirectInput
import Complexity.Models.TuringMachine.RedirectOutput

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Program.Enumeration
meta import Complexity.Control.Transition
meta import Complexity.Data.FinEnum
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Tapes
meta import Complexity.Data.Embedding
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Enumeration
meta import Complexity.Models.TuringMachine.Program.Word.Configuration
meta import Complexity.Models.TuringMachine.RedirectInput
meta import Complexity.Models.TuringMachine.RedirectOutput

open Complexity Complexity.TM

namespace ProgramCallCompiledTest

-- Arbitrary compiled control admits a finite numbering, also after redirection.
example {k : ℕ} {Γ α : Type} (p : TM.Program (Fin k) Γ α) :
    TM.Program (Fin k) Γ (p.State ⊕ p.Exit) := Program.call (Program.compile p)

example {κ τ : Type} [Fintype κ] [DecidableEq τ] {Γ α : Type}
    (p : TM.Program κ Γ α) (e : (κ ⊕ Unit) ↪ τ) :
    TM.Program τ Γ (p.State ⊕ p.Exit) :=
  Program.call (RedirectOutput.compilerAlong e (Program.compile p))

example {κ τ : Type} [Fintype κ] [DecidableEq τ] {α : Type}
    (p : TM.Program κ (Option Bool) α) (e : (κ ⊕ Unit) ↪ τ) :
    TM.Program τ (Option Bool) ((p.State ⊕ p.Exit) × Bool) :=
  Program.call (RedirectInput.compilerAlong e (Program.compile p))

def producer : TM.Program (Fin 0) (Option Bool) Unit := do
  Program.emit (some false)
  Program.emit (some true)

def copier : TM.Program (Fin 0) (Option Bool) Unit := do
  let a ← Program.readInput
  Program.emit a
  Program.moveInput 1
  let a ← Program.readInput
  Program.emit a

private def bufferEmbedding : (Fin 0 ⊕ Unit) ↪ Fin 1 where
  toFun _ := 0
  inj' := by decide

def composed : TM.Program (Fin 1) (Option Bool) Unit := do
  let _ ← Program.call (RedirectOutput.compilerAlong bufferEmbedding (Program.compile producer))
  Program.Word.rewind 0
  let _ ← Program.call (RedirectInput.compilerAlong bufferEmbedding (Program.compile copier))
  pure ()

-- Both called controllers came from Program, including the product added by input redirection.
#guard ((Program.compile (Program.call (Program.compile producer))).run (Input := List (Option Bool)) (Cfg (Fin 0) (Option Bool) ((Program.call producer.compile).State ⊕ (Program.call producer.compile).Exit) #[]) [] 2).output ==
  #[some false, some true]
-- Producer: 2 steps; rewinding two bits: 10; copier: 5.
#guard !(Program.compile composed).halt ((Program.compile composed).run (Input := List (Option Bool)) (Cfg (Fin 1) (Option Bool) (composed.State ⊕ composed.Exit) #[]) [] 16).state
#guard (Program.compile composed).halt ((Program.compile composed).run (Input := List (Option Bool)) (Cfg (Fin 1) (Option Bool) (composed.State ⊕ composed.Exit) #[]) [] 17).state
#guard ((Program.compile composed).run (Input := List (Option Bool)) (Cfg (Fin 1) (Option Bool) (composed.State ⊕ composed.Exit) #[]) [] 17).output == #[some false, some true]
#guard (((Program.compile composed).run (Input := List (Option Bool)) (Cfg (Fin 1) (Option Bool) (composed.State ⊕ composed.Exit) #[]) [] 17).workTapes 0)[(0 : ℤ)] == some false
#guard (((Program.compile composed).run (Input := List (Option Bool)) (Cfg (Fin 1) (Option Bool) (composed.State ⊕ composed.Exit) #[]) [] 17).workTapes 0)[(1 : ℤ)] == some true

end ProgramCallCompiledTest
