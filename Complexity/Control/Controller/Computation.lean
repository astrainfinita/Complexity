/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Cost
public import Mathlib.Data.Nat.Find

/-!
# Computing on inputs

`Basic`, `RunHistory` and `Cost` treat runs from an arbitrary configuration. Here a machine is a
computation from a standard input to an output. Two conventions fix the input and the output:
`HasConfig` gives the configuration type of each input and its initial configuration, and
`HasOutput` reads outputs from configurations. On top of them come the runs on a standard input
(`run`, `runWith`, `runHistory`), halting on an input (`Terminates`, `HaltsAt`), measurements of
these runs, and the complete specification `ComputesWith`. A lemma belongs here when it is the
counterpart, at `M.init input`, of a lemma about runs from an arbitrary configuration, or when it
is about a notion that needs the input and output conventions.
-/

@[expose] public section

universe u v

namespace Complexity.Controller

section Conventions

/-- Programs and machines with actions of type `Action` run on each standard input
`input : Input` with configurations of type `Config input`, starting from `init input`. The
instance depends only on the input type, so rewriting an input does not leave a stale instance. -/
class HasConfig (Action : Type*) (Input : Type*) (Config : outParam (Input → Type*)) where
  /-- The initial configuration on the standard input. -/
  init : (input : Input) → Config input

/-- How configurations of type `Config` are read as outputs of type `Output`. The class is keyed by
the configuration type alone, so an instance contains no input value; the generic interface asks
for an instance on every configuration type of the family, `∀ x, HasOutput (Config x) Output`. -/
class HasOutput (Config : Type*) (Output : outParam Type*) where
  /-- Whether a value is the output read from a configuration. -/
  IsOutput : Config → Output → Prop

initialize_simps_projections HasOutput (IsOutput → isOutput)

variable {F : Type (max u v) → Type*} {Observation : Type*} {Action : Type u} {Q : Type v}

/-- The initial machine configuration of `M` on the standard input `input`: its initial state
with the standard initial configuration. -/
def init {Input : Type*} {Config : Input → Type u} (M : Controller F Observation Action Q)
    (input : Input) [HasConfig Action Input Config] : Q × Config input :=
  (M.q₀, HasConfig.init Action input)

@[simp] theorem init_fst {Input : Type*} {Config : Input → Type u}
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config] :
    (M.init input).1 = M.q₀ := rfl

@[simp] theorem init_snd {Input : Type*} {Config : Input → Type u}
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config] :
    (M.init input).2 = HasConfig.init Action input := rfl

end Conventions

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

section Halting

variable (M : Controller Id Observation Action Q) (input : Input)

/-- The computation eventually reaches a halting state. -/
def Terminates [HasConfig Action Input Config] : Prop :=
  ∃ t, M.Halted (M.run input t)

/-- The first halting time, excluding the identity steps that pad a halted execution. -/
def HaltsAt [HasConfig Action Input Config] (t : ℕ) : Prop :=
  M.Halted (M.run input t) ∧ ∀ u < t, ¬M.Halted (M.run input u)

/-- Any halting endpoint contains a first halting time. -/
theorem exists_haltsAt_le [HasConfig Action Input Config] {t : ℕ}
    (h : M.Halted (M.run input t)) : ∃ n ≤ t, M.HaltsAt input n := by
  classical
  have h' : M.Terminates input := ⟨t, h⟩
  exact ⟨Nat.find h', Nat.find_min' h' h, Nat.find_spec h', fun _ hn ↦ Nat.find_min h' hn⟩

variable {M input} [HasConfig Action Input Config]

theorem HaltsAt.terminates {t : ℕ} (h : M.HaltsAt input t) : M.Terminates input := ⟨t, h.1⟩

theorem HaltsAt.unique {s t : ℕ} (h : M.HaltsAt input s) (h' : M.HaltsAt input t) : s = t := by
  rcases lt_trichotomy s t with h₁ | h₁ | h₁
  · exact (h'.2 s h₁ h.1).elim
  · exact h₁
  · exact (h.2 t h₁ h'.1).elim

theorem Terminates.exists_haltsAt (h : M.Terminates input) : ∃ t, M.HaltsAt input t :=
  let ⟨_, ht⟩ := h
  let ⟨n, _, hn⟩ := M.exists_haltsAt_le input ht
  ⟨n, hn⟩

end Halting

section Resources

variable (M : Controller Id Observation Action Q) {α : Type*} [SemilatticeSup α]

theorem actionSum_runHistory_mono (input : Input) [HasConfig Action Input Config]
    (cost : Action → Config input → ℕ) {n k : ℕ} (h : n ≤ k) :
    (M.runHistory input n).snd.actionSum cost ≤
      (M.runHistory input k).snd.actionSum cost :=
  M.actionSum_runHistoryFrom_mono cost (M.init input) h

theorem configSup_runHistory_mono (input : Input) [HasConfig Action Input Config]
    (space : Config input → α) {n k : ℕ} (h : n ≤ k) :
    (M.runHistory input n).snd.configSup space ≤
      (M.runHistory input k).snd.configSup space :=
  M.configSup_runHistoryFrom_mono space (M.init input) h

theorem config_le_configSup_runHistory (input : Input) [HasConfig Action Input Config]
    (space : Config input → α) {i n : ℕ} (h : i ≤ n) :
    space (M.run input i).2 ≤ (M.runHistory input n).snd.configSup space :=
  M.config_le_configSup_runHistoryFrom space (M.init input) h

theorem configSup_runHistory_le_iff (input : Input) [HasConfig Action Input Config]
    (space : Config input → α) (n : ℕ) (bound : α) :
    (M.runHistory input n).snd.configSup space ≤ bound ↔
      ∀ i ≤ n, space (M.run input i).2 ≤ bound :=
  M.configSup_runHistoryFrom_le_iff space (M.init input) n bound

end Resources

/-- One terminating run satisfies both budgets. The measurements read its history without the
control states. -/
def ComputesWith (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] [∀ x, HasOutput (Config x) Output] (output : Output)
    (timeCost spaceCost : History (Config input) Action → ℕ) (time space : ℕ) : Prop :=
  ∃ n, M.Halted (M.run input n) ∧ HasOutput.IsOutput (M.run input n).2 output ∧
    timeCost (M.runHistory input n).snd ≤ time ∧
    spaceCost (M.runHistory input n).snd ≤ space

variable {M : Controller Id Observation Action Q} {input : Input} [HasConfig Action Input Config]
  [∀ x, HasOutput (Config x) Output] {output : Output}
  {timeCost spaceCost : History (Config input) Action → ℕ} {time space : ℕ}

/-- Enlarging budgets preserves the same execution. -/
theorem computesWith_mono {time' space' : ℕ}
    (h : M.ComputesWith input output timeCost spaceCost time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesWith input output timeCost spaceCost time' space' := by
  obtain ⟨n, hn, ho, htime, hspace⟩ := h
  exact ⟨n, hn, ho, htime.trans ht, hspace.trans hs⟩

/-- An additive action budget bounds every prefix, including halted padding. -/
theorem computesWith_actionSum_le {cost : Action → Config input → ℕ}
    (h : M.ComputesWith input output (fun h ↦ h.actionSum cost) spaceCost time space) (u : ℕ) :
    (M.runHistory input u).snd.actionSum cost ≤ time := by
  obtain ⟨n, hn, _, ht, _⟩ := h
  by_cases hu : u ≤ n
  · exact (M.actionSum_runHistory_mono input cost hu).trans ht
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact ht

/-- A prefix-monotone history measurement bounds space throughout a computation. -/
theorem computesWith_space_le (h : M.ComputesWith input output timeCost spaceCost time space)
    (hmono : Monotone fun n ↦ spaceCost (M.runHistory input n).snd)
    (u : ℕ) : spaceCost (M.runHistory input u).snd ≤ space := by
  obtain ⟨n, hn, _, _, hs⟩ := h
  by_cases hu : u ≤ n
  · exact (hmono hu).trans hs
  · rw [M.runHistory_eq_of_halted input hn (by omega : n ≤ u)]
    exact hs

/-- A maximum configuration budget bounds every prefix, including halted padding. -/
theorem computesWith_configSup_le {size : Config input → ℕ}
    (h : M.ComputesWith input output timeCost (fun h ↦ h.configSup size) time space) (u : ℕ) :
    (M.runHistory input u).snd.configSup size ≤ space :=
  computesWith_space_le h (fun _ _ hn ↦ M.configSup_runHistory_mono input size hn) u

/-- Counting recorded actions describes the halted run at the advertised time bound. -/
theorem computesWith_unit_iff : M.ComputesWith input output History.length spaceCost time space ↔
      M.Halted (M.run input time) ∧
      HasOutput.IsOutput (M.run input time).2 output ∧
      spaceCost (M.runHistory input time).snd ≤ space := by
  constructor
  · rintro ⟨n, hn, ho, ht, hs⟩
    rw [History.length_snd] at ht
    have he : M.run input (M.runHistory input n).length =
        M.run input n := M.runFrom_length_runHistoryFrom (M.init input) n
    have hh := he.symm ▸ hn
    have hp := M.runHistory_eq_of_halted input hh (M.length_runHistory_le input n)
    have hq := M.runHistory_eq_of_halted input hh ht
    have hr := hq.trans hp.symm
    simpa only [← last_runHistory, hr] using And.intro hn (And.intro ho hs)
  · rintro ⟨hn, ho, hs⟩
    exact ⟨time, hn, ho, (History.length_snd _).trans_le (M.length_runHistory_le input time),
      hs⟩

end Complexity.Controller
