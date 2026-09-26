/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Configuration
public import Complexity.Control.Controller
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
  Controller F (Γ × (κ → Γ)) (TM.Action κ Γ Q) Q

namespace TM

variable {F : Type (max uκ u v) → Type*} {κ : Type uκ} {Γ : Type u} {Q : Type v}
  [Inhabited Γ] {xs : Array Γ}

/-- Initialize the raw configuration for a list input and read its output tape. -/
@[simps (attr := simp↓) init hasOutput]
instance rawExecution (xs : List Γ) :
    Controller.Execution (Cfg κ Γ Q xs.toArray)
      Q (Output := List Γ) (input := xs) where
  init q :=
    { state := q
      inputPos := ⟨1, by omega⟩
      workTapes := fun _ ↦ ∅
      workPos := fun _ ↦ 0
      output := #[] }
  state_init _ := rfl
  hasOutput cfg ys := cfg.output = ys.toArray

@[simp] theorem initInput_raw (M : TM F κ Γ Q) (xs : List Γ) :
    M.initInput (Config := Cfg κ Γ Q xs.toArray) xs =
      (rawExecution xs).init M.q₀ := rfl

/-- The deterministic step equation in terms of tape observations and actions. -/
theorem step_eq (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    M.step c = if M.halt c.state then c
      else apply
        ((M.transition c.state (c.inputSymbol, c.workSymbols)).run) c := rfl

/-- A transition moves each work head by at most one cell. -/
theorem step_workPos_bounds (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (i : κ) :
    c.workPos i - 1 ≤ (M.step c).workPos i ∧
      (M.step c).workPos i ≤ c.workPos i + 1 := by
  rw [step_eq]
  split
  · omega
  · exact Action.workPos_apply_bounds _ _ i

end TM

end Complexity
