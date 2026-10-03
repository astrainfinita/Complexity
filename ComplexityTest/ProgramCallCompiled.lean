/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Call

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
meta import Complexity.Data.Embedding
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Call
meta import Complexity.Models.TuringMachine.Program.Enumeration

open Complexity Complexity.TM

namespace ProgramCallCompiledTest

-- Arbitrary compiled control admits a finite numbering for calls.
example {k : ℕ} {Γ α : Type} (p : TM.Program (Fin k) Γ α) :
    TM.Program (Fin k) Γ (p.State ⊕ p.Exit) := Program.call (Program.compile p)

def producer : TM.Program (Fin 0) (Option Bool) Unit := do
  Program.emit (some false)
  Program.emit (some true)

-- A compiled program can itself be called and compiled again.
#guard ((Program.compile (Program.call (Program.compile producer))).run (Input := List (Option Bool)) (Cfg (Fin 0) (Option Bool) ((Program.call producer.compile).State ⊕ (Program.call producer.compile).Exit) #[]) [] 2).output ==
  #[some false, some true]

end ProgramCallCompiledTest
