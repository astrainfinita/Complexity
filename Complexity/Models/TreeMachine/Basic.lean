/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Configuration
public import Complexity.Control.Controller.Execution

/-!
# Tree register machines with atomic choices

Control observes the roots of a fixed register bank and selects one instruction: `nop`,
or a register operation whose first index is its destination. `F` describes the choices;
`Id` gives deterministic machines. The input tree starts in register zero, and every other
register starts empty. Execution uses the shared `Controller` API.
-/

@[expose] public section

universe u

namespace Complexity

/-- A controller whose atomic actions update one tree register. -/
abbrev TreeMachine (F : Type u → Type*) (k : ℕ) (Q : Type u) :=
  Controller F (Fin k → Bool) (TreeMachine.Action k Q) Q

namespace TreeMachine

variable {F : Type u → Type*} {k : ℕ} {Q : Type u}

/-- Initialize register zero and read the result from the same register. -/
instance [NeZero k] (a : Tree) :
    Controller.Execution (Cfg k Q) Q (Output := Tree) (input := a) where
  init q := ⟨q, input 0 a⟩
  state_init _ := rfl
  HasOutput cfg b := cfg.regs 0 = b

/-- Standard tree input places the value in register zero and clears all other registers. -/
@[simp] theorem initInput_tree [NeZero k] (M : TreeMachine F k Q) (a : Tree) :
    M.initInput (Config := Cfg k Q) a = ⟨M.q₀, input 0 a⟩ := rfl

/-- The deterministic step equation in terms of register roots and actions. -/
theorem step_eq (M : TreeMachine Id k Q) (c : Cfg k Q) :
    M.step c = if M.halt c.state then c else apply ((M.transition c.state (observe c)).run) c := rfl

end TreeMachine
end Complexity
