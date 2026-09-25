/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Basic

/-! # Fixed head movements -/

@[expose] public section

namespace Complexity.TM.Program

/-- Advance a selected head by a fixed number of cells. -/
def advance {κ : Type} [DecidableEq κ] {Γ : Type} (j : κ) : ℕ → Program κ Γ Unit
  | 0 => pure ()
  | n + 1 => do
    move j .pos
    advance j n

end Complexity.TM.Program
