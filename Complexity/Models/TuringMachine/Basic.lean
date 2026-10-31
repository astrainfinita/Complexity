/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Configuration
public import Complexity.Control.Controller.Basic
public import Complexity.Control.Controller.Execution

/-!
# Multi-tape Turing machines with explicit choices

A controller observes only the state and symbols under the heads and selects local actions
with choice shape `F`. `Id` gives deterministic machines.

Configurations store plain states and symbols. `Inhabited Γ` selects the blank symbol.
Execution uses the shared `Controller` API. Input, output, and resource accounting
remain specific to this storage model.
-/

@[expose] public section

universe uκ u v

namespace Complexity

/-- A multi-tape controller over the currently scanned input and work symbols. -/
abbrev TM (F : Type (max uκ u v) → Type*) (κ : Type uκ) (Γ : Type u) (Q : Type v) :=
  Controller F (Γ × (κ → Γ)) (TM.Action κ Γ) Q

namespace TM

variable {F : Type (max uκ u v) → Type*} {κ : Type uκ} {Γ : Type u} {Q : Type v}
  [Inhabited Γ] {xs : Array Γ}

variable (κ) in
/-- The standard initial configuration on a list input: the input head on the first symbol,
blank work tapes with their heads at zero, and no output. -/
@[simps -fullyApplied inputPos workTapes workPos output]
def Cfg.init (xs : List Γ) : Cfg κ Γ xs.toArray := ⟨1, fun _ ↦ ∅, fun _ ↦ 0, #[]⟩

instance : Controller.HasConfig (Action κ Γ) (List Γ) (fun xs ↦ Cfg κ Γ xs.toArray) where
  init xs := Cfg.init κ xs

@[simp] theorem hasConfig_init (xs : List Γ) :
    Controller.HasConfig.init (Action κ Γ) xs = Cfg.init κ xs := rfl

/-- Read the output tape as a list. -/
@[simps (attr := simp↓)]
instance rawExecution {xs : Array Γ} : Controller.Execution (Cfg κ Γ xs) (List Γ) where
  HasOutput cfg ys := cfg.output = ys.toArray

/-- The deterministic step equation in terms of tape observations and actions. -/
theorem step_eq (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) :
    M.step c = if M.halt c.1 then c
      else apply (M.transition c.1 (c.2.inputSymbol, c.2.workSymbols)).run c := rfl

/-- A transition moves each work head by at most one cell. -/
theorem step_workPos_bounds (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) (i : κ) :
    c.2.workPos i - 1 ≤ (M.step c).2.workPos i ∧
      (M.step c).2.workPos i ≤ c.2.workPos i + 1 := by
  rw [step_eq]
  split
  · omega
  · exact Action.workPos_apply_bounds _ c.2 i

end TM

end Complexity
