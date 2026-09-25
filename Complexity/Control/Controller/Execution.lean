/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Cost
public import Complexity.Control.Cost

/-!
# Execution with standard input and output

An execution instance fixes initialization and output interpretation for one input.
Control state is supplied by `HasState`; observations, actions, and local costs
are supplied separately when running the controller.
-/

@[expose] public section

universe u

namespace Complexity.Controller

/-- A standard input and output convention for one concrete configuration type. -/
class Execution {Input : Type*} (Config : Type*)
    (Q Output : outParam Type*) (input : Input)
    [HasState Config Q] where
  /-- Initialize a configuration from a control state. -/
  init : Q → Config
  /-- Initialization preserves the supplied control state. -/
  state_init : ∀ q, state (init q) = q
  /-- Interpret a configuration as an output value. -/
  hasOutput : Config → Output → Prop

variable {Input Output Observation Q : Type*} {Action Config : Type u}
    [HasState Config Q]

/-- The initial configuration selected by an execution convention. -/
def initInput {F : Type u → Type*} (M : Controller F Observation Action Q) (input : Input)
    [exe : Execution Config Q Output input] : Config :=
  exe.init M.q₀

@[simp] theorem state_initInput {F : Type u → Type*}
    (M : Controller F Observation Action Q) (input : Input)
    [Execution Config Q Output input] :
    state (M.initInput (Config := Config) input) = M.q₀ :=
  Execution.state_init M.q₀

variable [Observe Config Observation] [Apply Config Action]

variable (Config) in
/-- Run from the selected input configuration in the target monad. -/
def runWith {F : Type u → Type*} (m : Type u → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q)
    (input : Input) (n : ℕ) [Execution Config Q Output input] : m Config :=
  M.runFromWith m (M.initInput input) n

@[simp] theorem runWith_zero {F : Type u → Type*} (m : Type u → Type*)
    [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q)
    (input : Input) [Execution Config Q Output input] :
    M.runWith Config m input 0 = pure (M.initInput input) := rfl

variable (Config) in
/-- Run from the initial configuration selected by an execution convention. -/
def run (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [Execution Config Q Output input] : Config :=
  M.runFrom (M.initInput input) n

@[simp] theorem run_zero (M : Controller Id Observation Action Q) (input : Input)
    [Execution Config Q Output input] :
    M.run Config input 0 = M.initInput input := rfl

/-- One more step extends a standard input run. -/
theorem run_succ (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [Execution Config Q Output input] :
    M.run Config input (n + 1) = M.step (M.run Config input n) :=
  M.runFrom_succ' (M.initInput input) n

/-- Standard input execution stays fixed after reaching a halting state. -/
theorem run_eq_of_halted (M : Controller Id Observation Action Q) (input : Input)
    [Execution Config Q Output input] {n k : ℕ}
    (h : M.Halted (M.run Config input n)) (hk : n ≤ k) :
    M.run Config input k = M.run Config input n :=
  M.runFrom_eq_of_halted (M.initInput input) h hk

/-- The cumulative action cost of an execution prefix from its selected start. -/
def runActionSum (M : Controller Id Observation Action Q) (cost : Action → Config → ℕ)
    (input : Input) (n : ℕ) [Execution Config Q Output input] : ℕ :=
  M.runActionSumFrom cost (M.initInput input) n

/-- The peak configuration space of an execution prefix from its selected start. -/
def runConfigMax (M : Controller Id Observation Action Q)
    (space : Config → ℕ) (input : Input) (n : ℕ)
    [Execution Config Q Output input] : ℕ :=
  M.runConfigMaxFrom space (M.initInput input) n

@[simp] theorem runActionSum_zero (M : Controller Id Observation Action Q)
    (cost : Action → Config → ℕ) (input : Input)
    [Execution Config Q Output input] :
    runActionSum M cost input 0 = 0 := by
  simp [runActionSum]

@[simp] theorem runConfigMax_zero (M : Controller Id Observation Action Q)
    (space : Config → ℕ) (input : Input)
    [Execution Config Q Output input] :
    runConfigMax M space input 0 = space (M.initInput input) := by
  simp [runConfigMax]

section Resources

variable (M : Controller Id Observation Action Q)

theorem runActionSum_mono (cost : Action → Config → ℕ) (input : Input)
    [Execution Config Q Output input] {n k : ℕ} (h : n ≤ k) :
    M.runActionSum cost input n ≤ M.runActionSum cost input k :=
  M.runActionSumFrom_mono cost (M.initInput input) h

theorem runActionSum_eq_of_halted (cost : Action → Config → ℕ) (input : Input)
    [Execution Config Q Output input] {n k : ℕ}
    (h : M.Halted (M.run Config input n)) (hk : n ≤ k) :
    M.runActionSum cost input k = M.runActionSum cost input n :=
  M.runActionSumFrom_eq_of_halted cost (M.initInput input) h hk

theorem runConfigMax_mono (space : Config → ℕ) (input : Input)
    [Execution Config Q Output input] {n k : ℕ} (h : n ≤ k) :
    M.runConfigMax space input n ≤ M.runConfigMax space input k :=
  M.runConfigMaxFrom_mono space (M.initInput input) h

theorem runConfigMax_eq_of_halted (space : Config → ℕ) (input : Input)
    [Execution Config Q Output input] {n k : ℕ}
    (h : M.Halted (M.run Config input n)) (hk : n ≤ k) :
    M.runConfigMax space input k = M.runConfigMax space input n :=
  M.runConfigMaxFrom_eq_of_halted space (M.initInput input) h hk

theorem space_le_runConfigMax (space : Config → ℕ) (input : Input)
    [Execution Config Q Output input] {i n : ℕ} (h : i ≤ n) :
    space (M.run Config input i) ≤ M.runConfigMax space input n :=
  M.space_le_runConfigMaxFrom space (M.initInput input) h

theorem runConfigMax_le_iff (space : Config → ℕ) (input : Input)
    [Execution Config Q Output input] (n bound : ℕ) :
    M.runConfigMax space input n ≤ bound ↔ ∀ i ≤ n, space (M.run Config input i) ≤ bound :=
  M.runConfigMaxFrom_le_iff space (M.initInput input) n bound

end Resources

/-- One terminating execution satisfies both local resource budgets. -/
def computes (M : Controller Id Observation Action Q)
    (costs : CostModel Action Config)
    (input : Input) (output : Output) (time space : ℕ)
    [exe : Execution Config Q Output input] : Prop :=
  ∃ n,
    let final := M.run Config input n
    M.Halted final ∧ exe.hasOutput final output ∧
      runActionSum M costs.time input n ≤ time ∧
      runConfigMax M costs.space input n ≤ space

/-- Enlarging budgets preserves the same execution. -/
theorem computes_mono {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config}
    {input : Input} {output : Output} {time space time' space' : ℕ}
    [Execution Config Q Output input]
    (h : computes M costs input output time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    computes M costs input output time' space' := by
  obtain ⟨n, hn, ho, htime, hspace⟩ := h
  exact ⟨n, hn, ho, htime.trans ht, hspace.trans hs⟩

/-- A computation's action budget bounds every prefix, including halted padding. -/
theorem computes_runActionSum_le {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [Execution Config Q Output input]
    (h : computes M costs input output time space) (u : ℕ) :
    M.runActionSum costs.time input u ≤ time := by
  obtain ⟨n, hn, _, ht, _⟩ := h
  by_cases hu : u ≤ n
  · exact (M.runActionSum_mono costs.time input hu).trans ht
  · rw [M.runActionSum_eq_of_halted costs.time input hn (by omega : n ≤ u)]
    exact ht

/-- A computation's space budget bounds every prefix, including halted padding. -/
theorem computes_runConfigMax_le {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [Execution Config Q Output input]
    (h : computes M costs input output time space) (u : ℕ) :
    M.runConfigMax costs.space input u ≤ space := by
  obtain ⟨n, hn, _, _, hs⟩ := h
  by_cases hu : u ≤ n
  · exact (M.runConfigMax_mono costs.space input hu).trans hs
  · rw [M.runConfigMax_eq_of_halted costs.space input hn (by omega : n ≤ u)]
    exact hs

end Complexity.Controller
