/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Seek

meta import Complexity.Control.Program
meta import Complexity.Control.Program.Syntax
meta import Complexity.Control.Program.Compiler
meta import Complexity.Control.Transition
meta import Complexity.Data.IntMemory
meta import Complexity.Data.NatMemory
meta import Complexity.Models.TuringMachine.Basic
meta import Complexity.Models.TuringMachine.Configuration
meta import Complexity.Models.TuringMachine.Program.Basic
meta import Complexity.Models.TuringMachine.Program.Seek

open Complexity Complexity.TM

namespace ProgramSeekTest

-- The common scanner also supports rightward movement; each nonterminal cell costs three steps.
def search : TM.Program (Fin 1) Bool Unit := Program.seek 0 .pos (· = true)

def cfg : Cfg (Fin 1) Bool (search.State ⊕ search.Exit) #[] :=
  { (search.compile.initInput (Input := List Bool) (Config := Cfg _ _ _ [].toArray) []) with
    workTapes := fun _ ↦ IntMemory.ofArray #[false, false, true] }

#guard !search.compile.halt (search.compile.runFrom cfg 7).state
#guard search.compile.halt (search.compile.runFrom cfg 8).state
#guard (search.compile.runFrom cfg 8).workPos 0 == 2
#guard ((search.compile.runFrom cfg 8).workTapes 0)[(0 : ℤ)] == false
#guard ((search.compile.runFrom cfg 8).workTapes 0)[(1 : ℤ)] == false
#guard ((search.compile.runFrom cfg 8).workTapes 0)[(2 : ℤ)] == true
#guard (search.compile.runFrom cfg 8).inputPos == cfg.inputPos
#guard (search.compile.runFrom cfg 8).output == cfg.output

-- Starting at the delimiter still pays one dispatch and one read, with no movement.
def ready := { cfg with workPos := fun _ ↦ 2 }

#guard !search.compile.halt (search.compile.runFrom ready 1).state
#guard search.compile.halt (search.compile.runFrom ready 2).state
#guard (search.compile.runFrom ready 2).workPos 0 == 2

end ProgramSeekTest
