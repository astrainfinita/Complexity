/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Cost

/-!
# Execution with standard input and output

An execution instance fixes initialization and output interpretation for one input.
Control state is supplied by `HasState`; observations, actions, and resource measurements
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
  HasOutput : Config → Output → Prop

initialize_simps_projections Execution (HasOutput → hasOutput)

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

variable (Config) in
/-- Record the bounded execution from the selected standard input. -/
def runHistoryWith {F : Type u → Type*} (m : Type u → Type*)
    [Monad m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input) (n : ℕ) [Execution Config Q Output input] :
    m (History Config Action) :=
  M.runHistoryFromWith m (M.initInput input) n

variable (Config) in
/-- Record a deterministic execution from the selected standard input. -/
def runHistory (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [Execution Config Q Output input] : History Config Action :=
  M.runHistoryFrom (M.initInput input) n

@[simp] theorem runHistoryWith_zero {F : Type u → Type*} (m : Type u → Type*)
    [Monad m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input) [Execution Config Q Output input] :
    M.runHistoryWith Config m input 0 = pure (History.nil (M.initInput input)) := rfl

@[simp] theorem runHistory_zero (M : Controller Id Observation Action Q)
    (input : Input) [Execution Config Q Output input] :
    M.runHistory Config input 0 = History.nil (M.initInput input) := rfl

variable (Config) in
/-- A standard-input run records at most one action per unit of fuel. -/
theorem length_runHistory_le (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [Execution Config Q Output input] : (M.runHistory Config input n).length ≤ n :=
  M.length_runHistoryFrom_le (M.initInput input) n

@[simp] theorem last_runHistory (M : Controller Id Observation Action Q)
    (input : Input) (n : ℕ) [Execution Config Q Output input] :
    (M.runHistory Config input n).last = M.run Config input n :=
  M.last_runHistoryFrom (M.initInput input) n

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

/-- Standard-input histories stay fixed after reaching a halting state. -/
theorem runHistory_eq_of_halted (M : Controller Id Observation Action Q) (input : Input)
    [Execution Config Q Output input] {n k : ℕ}
    (h : M.Halted (M.run Config input n)) (hk : n ≤ k) :
    M.runHistory Config input k = M.runHistory Config input n :=
  M.runHistoryFrom_eq_of_halted (M.initInput input) h hk

section Resources

variable (M : Controller Id Observation Action Q) {α : Type*} [SemilatticeSup α]

theorem actionSum_runHistory_mono (cost : Action → Config → ℕ) (input : Input)
    [Execution Config Q Output input] {n k : ℕ} (h : n ≤ k) :
    (M.runHistory Config input n).actionSum cost ≤ (M.runHistory Config input k).actionSum cost :=
  M.actionSum_runHistoryFrom_mono cost (M.initInput input) h

theorem configSup_runHistory_mono (space : Config → α) (input : Input)
    [Execution Config Q Output input] {n k : ℕ} (h : n ≤ k) :
    (M.runHistory Config input n).configSup space ≤ (M.runHistory Config input k).configSup space :=
  M.configSup_runHistoryFrom_mono space (M.initInput input) h

theorem config_le_configSup_runHistory (space : Config → α) (input : Input)
    [Execution Config Q Output input] {i n : ℕ} (h : i ≤ n) :
    space (M.run Config input i) ≤ (M.runHistory Config input n).configSup space :=
  M.config_le_configSup_runHistoryFrom space (M.initInput input) h

theorem configSup_runHistory_le_iff (space : Config → α) (input : Input)
    [Execution Config Q Output input] (n : ℕ) (bound : α) :
    (M.runHistory Config input n).configSup space ≤ bound ↔
      ∀ i ≤ n, space (M.run Config input i) ≤ bound :=
  M.configSup_runHistoryFrom_le_iff space (M.initInput input) n bound

end Resources

/-- One terminating history satisfies both budgets under the chosen history measurements. -/
def ComputesWith (M : Controller Id Observation Action Q)
    (timeCost spaceCost : History Config Action → ℕ)
    (input : Input) (output : Output) (time space : ℕ)
    [exe : Execution Config Q Output input] : Prop :=
  ∃ n,
    let final := M.run Config input n
    let history := M.runHistory Config input n
    M.Halted final ∧ exe.HasOutput final output ∧
      timeCost history ≤ time ∧ spaceCost history ≤ space

variable {M : Controller Id Observation Action Q}
  {timeCost spaceCost : History Config Action → ℕ}
  {input : Input} {output : Output} {time space : ℕ}

/-- Enlarging budgets preserves the same execution. -/
theorem computesWith_mono [Execution Config Q Output input] {time' space' : ℕ}
    (h : M.ComputesWith timeCost spaceCost input output time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesWith timeCost spaceCost input output time' space' := by
  obtain ⟨n, hn, ho, htime, hspace⟩ := h
  exact ⟨n, hn, ho, htime.trans ht, hspace.trans hs⟩

/-- An additive action budget bounds every prefix, including halted padding. -/
theorem computesWith_actionSum_le [Execution Config Q Output input]
    {cost : Action → Config → ℕ}
    (h : M.ComputesWith (fun h ↦ h.actionSum cost) spaceCost input output time space) (u : ℕ) :
    (M.runHistory Config input u).actionSum cost ≤ time := by
  obtain ⟨n, hn, _, ht, _⟩ := h
  by_cases hu : u ≤ n
  · exact (M.actionSum_runHistory_mono cost input hu).trans ht
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact ht

/-- A prefix-monotone history measurement bounds space throughout a computation. -/
theorem computesWith_space_le [Execution Config Q Output input]
    (h : M.ComputesWith timeCost spaceCost input output time space)
    (hmono : Monotone fun n ↦ spaceCost (M.runHistory Config input n))
    (u : ℕ) : spaceCost (M.runHistory Config input u) ≤ space := by
  obtain ⟨n, hn, _, _, hs⟩ := h
  by_cases hu : u ≤ n
  · exact (hmono hu).trans hs
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact hs

/-- A maximum configuration budget bounds every prefix, including halted padding. -/
theorem computesWith_configSup_le [Execution Config Q Output input] {size : Config → ℕ}
    (h : M.ComputesWith timeCost (fun h ↦ h.configSup size) input output time space) (u : ℕ) :
    (M.runHistory Config input u).configSup size ≤ space :=
  computesWith_space_le h (fun _ _ hn ↦ M.configSup_runHistory_mono size input hn) u

/-- Counting recorded actions describes the halted run at the advertised time bound. -/
theorem computesWith_unit_iff [exe : Execution Config Q Output input] :
    M.ComputesWith History.length spaceCost input output time space ↔
      M.Halted (M.run Config input time) ∧
      exe.HasOutput (M.run Config input time) output ∧
      spaceCost (M.runHistory Config input time) ≤ space := by
  unfold ComputesWith
  constructor
  · rintro ⟨n, hn, ho, ht, hs⟩
    have he : M.run Config input (M.runHistory Config input n).length =
        M.run Config input n := M.runFrom_length_runHistoryFrom (M.initInput input) n
    have hh := he.symm ▸ hn
    have hp := M.runHistory_eq_of_halted input hh (M.length_runHistory_le Config input n)
    have hq := M.runHistory_eq_of_halted input hh ht
    have hr := hq.trans hp.symm
    simpa only [← last_runHistory, hr] using And.intro hn (And.intro ho hs)
  · rintro ⟨hn, ho, hs⟩
    exact ⟨time, hn, ho, M.length_runHistory_le Config input time, hs⟩

end Complexity.Controller
