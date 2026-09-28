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
    [Monad m] [LawfulApplicative m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input) [Execution Config Q Output input] :
    M.runHistoryWith Config m input 0 = pure (History.nil (M.initInput input)) :=
  M.runHistoryFromWith_zero m (M.initInput input)

@[simp] theorem runHistory_zero (M : Controller Id Observation Action Q)
    (input : Input) [Execution Config Q Output input] :
    M.runHistory Config input 0 = History.nil (M.initInput input) := rfl

variable (Config) in
/-- Standard-input execution satisfies the common bounded-run conditions. -/
theorem runHistory_spec (M : Controller Id Observation Action Q) (input : Input) (n : ℕ)
    [Execution Config Q Output input] :
    M.RunConditions (M.initInput input) n (M.runHistory Config input n) :=
  M.runHistoryFrom_spec (M.initInput input) n

@[simp] theorem last_runHistoryWith {F : Type u → Type*} (m : Type u → Type*)
    [Monad m] [LawfulMonad m] [MonadLiftT F m] (M : Controller F Observation Action Q)
    (input : Input) (n : ℕ) [Execution Config Q Output input] :
    (fun h ↦ h.last) <$> M.runHistoryWith Config m input n = M.runWith Config m input n :=
  M.last_runHistoryFromWith m (M.initInput input) n

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

/-- One terminating history satisfies both resource budgets. -/
def computes (M : Controller Id Observation Action Q)
    (costs : CostModel Action Config)
    (input : Input) (output : Output) (time space : ℕ)
    [exe : Execution Config Q Output input] : Prop :=
  ∃ n,
    let history := M.runHistory Config input n
    M.Halted history.last ∧ exe.hasOutput history.last output ∧
      costs.time history ≤ time ∧ costs.space history ≤ space

/-- The endpoint of a computation agrees with the ordinary standard-input run. -/
theorem computes_iff {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [exe : Execution Config Q Output input] :
    M.computes costs input output time space ↔
      ∃ n, M.Halted (M.run Config input n) ∧ exe.hasOutput (M.run Config input n) output ∧
        costs.time (M.runHistory Config input n) ≤ time ∧
        costs.space (M.runHistory Config input n) ≤ space := by
  simp only [computes, last_runHistory]

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

/-- An additive action budget bounds every prefix, including halted padding. -/
theorem computes_runActionSum_le {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [Execution Config Q Output input] {cost : Action → Config → ℕ}
    (htime : costs.time = fun h ↦ h.actionSum cost)
    (h : computes M costs input output time space) (u : ℕ) :
    M.runActionSum cost input u ≤ time := by
  obtain ⟨n, hn, _, ht, _⟩ := computes_iff.mp h
  rw [htime] at ht
  by_cases hu : u ≤ n
  · exact (M.runActionSum_mono cost input hu).trans ht
  · rw [M.runActionSum_eq_of_halted cost input hn (by omega : n ≤ u)]
    exact ht

/-- A prefix-monotone history measurement bounds space throughout a computation. -/
theorem computes_space_le {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [Execution Config Q Output input]
    (h : computes M costs input output time space)
    (hmono : Monotone fun n ↦ costs.space (M.runHistory Config input n))
    (u : ℕ) : costs.space (M.runHistory Config input u) ≤ space := by
  obtain ⟨n, hn, _, _, hs⟩ := computes_iff.mp h
  by_cases hu : u ≤ n
  · exact (hmono hu).trans hs
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact hs

/-- A maximum configuration budget bounds every prefix, including halted padding. -/
theorem computes_runConfigMax_le {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {time space : ℕ}
    [Execution Config Q Output input] {size : Config → ℕ}
    (hspace : costs.space = fun h ↦ h.configSup size)
    (h : computes M costs input output time space) (u : ℕ) :
    M.runConfigMax size input u ≤ space := by
  have hm : Monotone fun n ↦ costs.space (M.runHistory Config input n) := by
    rw [hspace]
    exact fun _ _ hn ↦ M.runConfigMax_mono size input hn
  simpa only [hspace, runConfigMax, runConfigMaxFrom, runHistory] using computes_space_le h hm u

/-- Counting recorded actions describes the halted run at the advertised time bound. -/
theorem computes_unit_iff {M : Controller Id Observation Action Q}
    {costs : CostModel Action Config} {input : Input} {output : Output} {t s : ℕ}
    [exe : Execution Config Q Output input]
    (htime : costs.time = History.length) :
    M.computes costs input output t s ↔
      M.Halted (M.run Config input t) ∧
      exe.hasOutput (M.run Config input t) output ∧
      costs.space (M.runHistory Config input t) ≤ s := by
  rw [computes_iff]
  constructor
  · rintro ⟨n, hn, ho, ht, hs⟩
    rw [htime] at ht
    have he : M.run Config input (M.runHistory Config input n).length =
        M.run Config input n := by
      simpa only [run, runHistory] using
        M.runFrom_length_runHistoryFrom (M.initInput (Config := Config) input) n
    have hh := he.symm ▸ hn
    have hp := M.runHistory_eq_of_halted input hh (M.runHistory_spec Config input n).length_le
    have hq := M.runHistory_eq_of_halted input hh ht
    have hr := hq.trans hp.symm
    have he' := congrArg History.last hr
    simp only [last_runHistory] at he'
    exact ⟨he'.symm ▸ hn, he'.symm ▸ ho, hr.symm ▸ hs⟩
  · rintro ⟨hn, ho, hs⟩
    exact ⟨t, hn, ho, htime.symm ▸ (M.runHistory_spec Config input t).length_le, hs⟩

end Complexity.Controller
