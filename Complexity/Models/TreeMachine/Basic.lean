/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Configuration
public import Complexity.Control.Controller.Computation

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
  Controller F (Fin k → Bool) (TreeMachine.Action k) Q

namespace TreeMachine

variable {F : Type u → Type*} {k : ℕ} {Q : Type u}

variable (k) in
/-- The standard initial register bank: the input in register zero, every other register
empty. -/
@[simps -fullyApplied]
def Cfg.init [NeZero k] (a : Tree) : Cfg k := ⟨input 0 a⟩

instance [NeZero k] : Controller.HasConfig (Action k) Tree (fun _ ↦ Cfg k) where
  init a := Cfg.init k a

@[simp] theorem hasConfig_init [NeZero k] (a : Tree) :
    Controller.HasConfig.init (Action k) a = Cfg.init k a := rfl

/-- Read the result from register zero. -/
@[simps -isSimp]
instance hasOutput [NeZero k] : Controller.HasOutput (Cfg k) Tree where
  IsOutput cfg b := cfg.regs 0 = b

/-- The deterministic step equation in terms of register roots and actions. -/
theorem step_eq (M : TreeMachine Id k Q) (c : Q × Cfg k) :
    M.step c = if M.halt c.1 then c else apply (M.transition c.1 (observe c.2)).run c := rfl

end TreeMachine
end Complexity
