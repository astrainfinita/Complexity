/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Configuration
public import Complexity.Control.Controller.Execution

/-! # Multiple-stack machines with finite local observations -/

@[expose] public section

universe uκ u v

namespace Complexity

/-- A controller observing the input symbol and the top of each work stack. -/
abbrev StackMachine (F : Type (max uκ u v) → Type*)
    (κ : Type uκ) (Γ : Type u) (Q : Type v) :=
  Controller F (Option Γ × (κ → Option Γ)) (StackMachine.Action κ Γ Q) Q

namespace StackMachine

variable {κ : Type uκ} {Γ : Type u} {Q : Type v}

/-- All work stacks start empty; input and output are ordinary symbol lists. -/
@[simps (attr := simp↓) init hasOutput]
instance execution (xs : List Γ) :
    Controller.Execution (Cfg κ Γ Q xs.toArray) Q (Output := List Γ) (input := xs) where
  init q :=
    { state := q
      inputPos := ⟨1, by omega⟩
      «stacks» := fun _ ↦ []
      output := #[] }
  state_init _ := rfl
  hasOutput c ys := c.output = ys.toArray

end StackMachine
end Complexity
