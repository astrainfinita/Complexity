/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Configuration
public import Complexity.Control.Controller
public import Complexity.Control.Controller.Execution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Multi-tape Turing machines with explicit choices

A controller observes only the state and symbols under the heads and selects local actions
with choice shape `F`. Execution interprets each choice in a separate monad. `Id` gives
deterministic machines; `Choice.Binary` permits exactly two labelled alternatives per step.

Configurations store plain states and symbols. `Inhabited Γ` selects the blank symbol.
Execution from a configuration uses the shared `Controller.step`, `Controller.runFrom`,
and `Controller.runTrace` APIs, or their `With` variants for an explicit choice interpretation.
Input, output, and resource accounting remain specific to this storage model.
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

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Positions visited on a work tape along an externally recorded trace. -/
def visitedOfTrace (cs : List (Cfg κ Γ Q xs)) (i : κ) : Finset ℤ :=
  (cs.map fun c ↦ c.workPos i).toFinset

/-- Work space used by one trace, with input and output excluded.
A concrete branching model determines which traces its resource bounds quantify over. -/
def spaceUsedOfTrace [Fintype κ] (cs : List (Cfg κ Γ Q xs)) : ℕ :=
  ∑ i : κ, (visitedOfTrace cs i).card

end TM

end Complexity
