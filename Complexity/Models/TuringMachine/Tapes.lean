/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Configuration

/-! # Selecting work tapes

A work layout selects the source tapes while preserving input, output, and control.
-/

@[expose] public section

namespace Complexity.TM

variable {κ τ Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Keep the tapes selected by a layout, without changing input, output, or control. -/
@[simps]
def Cfg.restrictWorkAlong (L : κ ↪ τ) (c : Cfg τ Γ Q xs) : Cfg κ Γ Q xs where
  state := c.state
  inputPos := c.inputPos
  workTapes := c.workTapes ∘ L
  workPos := c.workPos ∘ L
  output := c.output

end Complexity.TM
