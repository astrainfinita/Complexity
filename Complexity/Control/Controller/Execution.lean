/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Cost

/-!
# Execution with standard input and output

A machine runs from its initial configuration `M.init input`, its initial control state paired
with the standard configuration given by `HasConfig`, so running a machine needs no configuration
type. `Execution` interprets configurations of one type as outputs. Observations,
actions, and resource measurements are supplied separately when running the controller.
-/

@[expose] public section

universe u v

namespace Complexity.Controller

/-- An output convention for one configuration type. -/
class Execution (Config : Type*) (Output : outParam Type*) where
  /-- Interpret a configuration as an output value. -/
  HasOutput : Config → Output → Prop

initialize_simps_projections Execution (HasOutput → hasOutput)

variable {F : Type (max u v) → Type*} {Input Output Observation : Type*} {Action : Type u}
  {Config : Input → Type u} {Q : Type v} [∀ x, Observe (Config x) Observation]
  [∀ x, Apply (Config x) Action]

/-- Run `M` from its initial configuration on the standard input, in the target monad. -/
def runWith (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q)
    (input : Input) (n : ℕ)
    [HasConfig Action Input Config] : m (Q × Config input) :=
  M.runFromWith m (M.init input) n

@[simp] theorem runWith_zero (m : Type (max u v) → Type*)
    [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q)
    (input : Input)
    [HasConfig Action Input Config] :
    M.runWith m input 0 = pure (M.init input) := rfl

/-- Run `M` from its initial configuration on the standard input. -/
def run (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [HasConfig Action Input Config] : Q × Config input :=
  M.runFrom (M.init input) n

@[simp] theorem run_zero (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] :
    M.run input 0 = M.init input := rfl

/-- Record the bounded execution from the selected standard input. -/
def runHistoryWith (m : Type (max u v) → Type*)
    [Monad m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input) (n : ℕ)
    [HasConfig Action Input Config] :
    m (History (Q × Config input) (Q × Action)) :=
  M.runHistoryFromWith m (M.init input) n

/-- Record a deterministic execution from the selected standard input. -/
def runHistory (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [HasConfig Action Input Config] : History (Q × Config input) (Q × Action) :=
  M.runHistoryFrom (M.init input) n

@[simp] theorem runHistoryWith_zero (m : Type (max u v) → Type*)
    [Monad m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input)
    [HasConfig Action Input Config] :
    M.runHistoryWith m input 0 = pure (History.nil (M.init input)) := rfl

@[simp] theorem runHistory_zero (M : Controller Id Observation Action Q)
    (input : Input)
    [HasConfig Action Input Config] :
    M.runHistory input 0 = History.nil (M.init input) := rfl

/-- A standard-input run records at most one action per unit of fuel. -/
theorem length_runHistory_le (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [HasConfig Action Input Config] : (M.runHistory input n).length ≤ n :=
  M.length_runHistoryFrom_le (M.init input) n

@[simp] theorem last_runHistory (M : Controller Id Observation Action Q)
    (input : Input) (n : ℕ)
    [HasConfig Action Input Config] :
    (M.runHistory input n).last = M.run input n :=
  M.last_runHistoryFrom (M.init input) n

/-- One more step extends a standard input run. -/
theorem run_succ (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [HasConfig Action Input Config] :
    M.run input (n + 1) = M.step (M.run input n) :=
  M.runFrom_succ' (M.init input) n

/-- Standard input execution stays fixed after reaching a halting state. -/
theorem run_eq_of_halted (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] {n k : ℕ}
    (h : M.Halted (M.run input n)) (hk : n ≤ k) :
    M.run input k = M.run input n :=
  M.runFrom_eq_of_halted (M.init input) h hk

/-- Standard-input histories stay fixed after reaching a halting state. -/
theorem runHistory_eq_of_halted (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] {n k : ℕ}
    (h : M.Halted (M.run input n)) (hk : n ≤ k) :
    M.runHistory input k = M.runHistory input n :=
  M.runHistoryFrom_eq_of_halted (M.init input) h hk

section Resources

variable (M : Controller Id Observation Action Q) {α : Type*} [SemilatticeSup α]

theorem actionSum_runHistory_mono (input : Input) [HasConfig Action Input Config]
    (cost : Q × Action → Q × Config input → ℕ) {n k : ℕ} (h : n ≤ k) :
    (M.runHistory input n).actionSum cost ≤ (M.runHistory input k).actionSum cost :=
  M.actionSum_runHistoryFrom_mono cost (M.init input) h

theorem configSup_runHistory_mono (input : Input) [HasConfig Action Input Config]
    (space : Q × Config input → α) {n k : ℕ} (h : n ≤ k) :
    (M.runHistory input n).configSup space ≤ (M.runHistory input k).configSup space :=
  M.configSup_runHistoryFrom_mono space (M.init input) h

theorem config_le_configSup_runHistory (input : Input) [HasConfig Action Input Config]
    (space : Q × Config input → α) {i n : ℕ} (h : i ≤ n) :
    space (M.run input i) ≤ (M.runHistory input n).configSup space :=
  M.config_le_configSup_runHistoryFrom space (M.init input) h

theorem configSup_runHistory_le_iff (input : Input) [HasConfig Action Input Config]
    (space : Q × Config input → α)
    (n : ℕ) (bound : α) :
    (M.runHistory input n).configSup space ≤ bound ↔
      ∀ i ≤ n, space (M.run input i) ≤ bound :=
  M.configSup_runHistoryFrom_le_iff space (M.init input) n bound

end Resources

/-- One terminating history satisfies both budgets under the chosen history measurements. -/
def ComputesWith (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] [∀ x, Execution (Config x) Output] (output : Output)
    (timeCost spaceCost : History (Q × Config input) (Q × Action) → ℕ) (time space : ℕ) : Prop :=
  ∃ n,
    let final := M.run input n
    let history := M.runHistory input n
    M.Halted final ∧ Execution.HasOutput final.2 output ∧
      timeCost history ≤ time ∧ spaceCost history ≤ space

variable {M : Controller Id Observation Action Q} {input : Input} [HasConfig Action Input Config]
  [∀ x, Execution (Config x) Output] {output : Output}
  {timeCost spaceCost : History (Q × Config input) (Q × Action) → ℕ} {time space : ℕ}

/-- Enlarging budgets preserves the same execution. -/
theorem computesWith_mono {time' space' : ℕ}
    (h : M.ComputesWith input output timeCost spaceCost time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesWith input output timeCost spaceCost time' space' := by
  obtain ⟨n, hn, ho, htime, hspace⟩ := h
  exact ⟨n, hn, ho, htime.trans ht, hspace.trans hs⟩

/-- An additive action budget bounds every prefix, including halted padding. -/
theorem computesWith_actionSum_le {cost : Q × Action → Q × Config input → ℕ}
    (h : M.ComputesWith input output (fun h ↦ h.actionSum cost) spaceCost time space) (u : ℕ) :
    (M.runHistory input u).actionSum cost ≤ time := by
  obtain ⟨n, hn, _, ht, _⟩ := h
  by_cases hu : u ≤ n
  · exact (M.actionSum_runHistory_mono input cost hu).trans ht
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact ht

/-- A prefix-monotone history measurement bounds space throughout a computation. -/
theorem computesWith_space_le (h : M.ComputesWith input output timeCost spaceCost time space)
    (hmono : Monotone fun n ↦ spaceCost (M.runHistory input n))
    (u : ℕ) : spaceCost (M.runHistory input u) ≤ space := by
  obtain ⟨n, hn, _, _, hs⟩ := h
  by_cases hu : u ≤ n
  · exact (hmono hu).trans hs
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact hs

/-- A maximum configuration budget bounds every prefix, including halted padding. -/
theorem computesWith_configSup_le {size : Q × Config input → ℕ}
    (h : M.ComputesWith input output timeCost (fun h ↦ h.configSup size) time space) (u : ℕ) :
    (M.runHistory input u).configSup size ≤ space :=
  computesWith_space_le h (fun _ _ hn ↦ M.configSup_runHistory_mono input size hn) u

/-- Counting recorded actions describes the halted run at the advertised time bound. -/
theorem computesWith_unit_iff : M.ComputesWith input output History.length spaceCost time space ↔
      M.Halted (M.run input time) ∧
      Execution.HasOutput (M.run input time).2 output ∧
      spaceCost (M.runHistory input time) ≤ space := by
  unfold ComputesWith
  constructor
  · rintro ⟨n, hn, ho, ht, hs⟩
    have he : M.run input (M.runHistory input n).length =
        M.run input n := M.runFrom_length_runHistoryFrom (M.init input) n
    have hh := he.symm ▸ hn
    have hp := M.runHistory_eq_of_halted input hh (M.length_runHistory_le input n)
    have hq := M.runHistory_eq_of_halted input hh ht
    have hr := hq.trans hp.symm
    simpa only [← last_runHistory, hr] using And.intro hn (And.intro ho hs)
  · rintro ⟨hn, ho, hs⟩
    exact ⟨time, hn, ho, M.length_runHistory_le input time, hs⟩

end Complexity.Controller
