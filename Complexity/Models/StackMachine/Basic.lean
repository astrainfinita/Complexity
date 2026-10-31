/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Configuration
public import Complexity.Control.Controller.Computation

/-! # Multiple-stack machines with finite local observations -/

@[expose] public section

universe uκ u v

namespace Complexity

/-- A controller observing the input symbol and the top of each work stack. -/
abbrev StackMachine (F : Type (max uκ u v) → Type*)
    (κ : Type uκ) (Γ : Type u) (Q : Type v) :=
  Controller F (Option Γ × (κ → Option Γ)) (StackMachine.Action κ Γ) Q

namespace StackMachine

variable {κ : Type uκ} {Γ : Type u}

variable (κ) in
/-- The standard initial configuration on a list input: the input head on the first symbol,
empty work stacks, and no output. -/
@[simps -fullyApplied inputPos «stacks» output]
def Cfg.init (xs : List Γ) : Cfg κ Γ xs.toArray := ⟨1, fun _ ↦ [], #[]⟩

instance : Controller.HasConfig (Action κ Γ) (List Γ) (fun xs ↦ Cfg κ Γ xs.toArray) where
  init xs := Cfg.init κ xs

@[simp] theorem hasConfig_init (xs : List Γ) :
    Controller.HasConfig.init (Action κ Γ) xs = Cfg.init κ xs := rfl

/-- Input and output are ordinary symbol lists. -/
@[simps (attr := simp↓)]
instance hasOutput {xs : Array Γ} : Controller.HasOutput (Cfg κ Γ xs) (List Γ) where
  IsOutput c ys := c.output = ys.toArray

end StackMachine

end Complexity
