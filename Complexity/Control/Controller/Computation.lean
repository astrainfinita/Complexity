/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Cost
public import Complexity.Control.Transition.Simulation
public import Mathlib.Data.Nat.Find

/-!
# Computing on inputs

`Basic`, `RunHistory` and `Cost` treat runs from an arbitrary configuration. Here a machine is a
computation from a standard input to an output. Two conventions fix the input and the output:
`HasConfig` gives the configuration type of each input and its initial configuration, and
`HasOutput` reads outputs from configurations. On top of them come the runs on a standard input
(`run`, `runWith`, `runHistory`) and the histories they can return at any depth (`histories`),
computing within budgets in every interpretation (`ComputesInWith`), halting on an input
(`Terminates`, `HaltsAt`), measurements of these runs, and the complete deterministic
specification `ComputesWith`. A lemma belongs here when it is the counterpart, at `M.init input`,
of a lemma about runs from an arbitrary configuration, or when it is about a notion that needs the
input and output conventions.

`ComputesInWith` bounds every history at every depth, so on `Id` it agrees with `ComputesWith`,
which reads only the halting history, when the measurements are monotone along the run, as length
and space are. Its outputs live in the same interpretation as the run: on `Multiset` they are the
outputs of all branches with their multiplicities. The output type lives in the universe of the
results, `Type (max u v)`; this is a current limitation, not a decision. The way halting is
stated, inside the correspondence at one step of the run, and the difference from `ComputesWith`
are the current state too: the deterministic definition is to become the instance on `Id`.
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

/-- Once every value a standard-input run can return has halted, more steps leave the run
unchanged. -/
theorem runWith_eq_of_forall_halted (m : Type (max u v) → Type*) [Monad m] [LawfulMonad m]
    [MonadLiftT F m] [MonadReturns m] (M : Controller F Observation Action Q) (input : Input)
    [HasConfig Action Input Config] {n k : ℕ}
    (h : ∀ c ∈ returns (M.runWith m input n), M.Halted c) (hk : n ≤ k) :
    M.runWith m input k = M.runWith m input n :=
  M.runFromWith_eq_of_forall_halted m (M.init input) h hk

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

/-- A standard-input run that has halted by step `t` records at most `t` actions at every
depth. -/
theorem length_runHistory_le_of_halted (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] {t : ℕ} (h : M.Halted (M.run input t)) (n : ℕ) :
    (M.runHistory input n).length ≤ t := by
  rcases le_total n t with hn | hn
  · exact (M.length_runHistory_le input n).trans hn
  · exact M.runHistory_eq_of_halted input h hn ▸ M.length_runHistory_le input t

/-- The histories that a run of `M` on the standard input can return, at any depth. They include
every finite prefix of every branch. -/
def histories (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m] [MonadReturns m]
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config] :
    Set (History (Q × Config input) (Q × Action)) :=
  ⋃ n, returns (M.runHistoryWith m input n)

section Histories

variable (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m] [MonadReturns m]
  (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config]

theorem mem_histories_iff {h : History (Q × Config input) (Q × Action)} :
    h ∈ M.histories m input ↔ ∃ n, h ∈ returns (M.runHistoryWith m input n) :=
  Set.mem_iUnion

theorem forall_mem_histories_iff {P : History (Q × Config input) (Q × Action) → Prop} :
    (∀ h ∈ M.histories m input, P h) ↔ ∀ n, ∀ h ∈ returns (M.runHistoryWith m input n), P h := by
  simp only [mem_histories_iff, forall_exists_index]
  exact forall_comm

variable [LawfulMonad m]

/-- A step invariant holds for every history. -/
theorem forall_mem_histories {P : History (Q × Config input) (Q × Action) → Prop}
    (hinit : P (History.nil (M.init input)))
    (hstep : ∀ h, P h → ∀ h' ∈ returns (M.stepWith m h), P h') :
    ∀ h ∈ M.histories m input, P h :=
  (M.forall_mem_histories_iff m input).2 fun n ↦ M.forall_mem_runFromWith m hstep hinit n

/-- Once every value a run can return at step `t` has halted, no history is longer than `t`. -/
theorem length_le_of_forall_halted {t : ℕ}
    (ht : ∀ c ∈ returns (M.runWith m input t), M.Halted c) :
    ∀ h ∈ M.histories m input, h.length ≤ t := by
  refine (M.forall_mem_histories_iff m input).2 fun n h hh ↦ ?_
  by_cases hn : n ≤ t
  · exact (M.runHistoryFromWith_spec m (M.init input) n h hh).length_le.trans hn
  · have ht' : ∀ p ∈ returns (M.runHistoryFromWith m (M.init input) t), M.Halted p :=
      fun p hp ↦ ht p.last (by
        rw [runWith, ← M.last_runHistoryFromWith m, mem_returns_map_iff]; exact ⟨p, hp, rfl⟩)
    rw [runHistoryWith, runHistoryFromWith,
      M.runFromWith_eq_of_forall_halted m _ ht' (Nat.le_of_not_ge hn)] at hh
    exact (M.runHistoryFromWith_spec m (M.init input) t h hh).length_le

/-- If no history is longer than `t`, every value a run can return at step `t + 1` has halted:
a branch still running after `t` steps would have a longer history at the next step, or has no
successor and is gone. -/
theorem forall_halted_succ_of_forall_length_le {t : ℕ}
    (hl : ∀ h ∈ M.histories m input, h.length ≤ t) :
    ∀ c ∈ returns (M.runWith m input (t + 1)), M.Halted c := by
  intro c hc
  rw [runWith, ← M.last_runHistoryFromWith m, mem_returns_map_iff] at hc
  obtain ⟨h, hh, rfl⟩ := hc
  exact (M.runHistoryFromWith_spec m (M.init input) (t + 1) h hh).stopped.resolve_left
    fun hlen ↦ absurd (hl h ((M.mem_histories_iff m input).2 ⟨t + 1, hh⟩)) (by omega)

end Histories

section ComputesInWith

variable {Output : Type (max u v)}

/-- `M` computes `outputs` from `input` in the interpretation `m` within both budgets: on every
history the two measurements are within budget, and at some step the results of the run correspond
to `outputs` branch by branch, each branch halted with the corresponding output. -/
def ComputesInWith (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m] [MonadReturns m]
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config]
    [∀ x, HasOutput (Config x) Output] (outputs : m Output)
    (timeCost spaceCost : History (Config input) Action → ℕ) (time space : ℕ) : Prop :=
  (∀ h ∈ M.histories m input, timeCost h.snd ≤ time ∧ spaceCost h.snd ≤ space) ∧
  ∃ n, LiftRel (fun c y ↦ M.Halted c ∧ HasOutput.IsOutput c.2 y) (M.runWith m input n) outputs

variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT F m] [MonadReturns m]
  {M : Controller F Observation Action Q} {input : Input} [HasConfig Action Input Config]
  [∀ x, HasOutput (Config x) Output] {outputs : m Output}
  {timeCost spaceCost : History (Config input) Action → ℕ} {time space : ℕ}

/-- Enlarging budgets keeps the same outputs. -/
theorem computesInWith_mono {time' space' : ℕ}
    (h : M.ComputesInWith m input outputs timeCost spaceCost time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesInWith m input outputs timeCost spaceCost time' space' :=
  ⟨fun h' hh ↦ (h.1 h' hh).imp (·.trans ht) (·.trans hs), h.2⟩

end ComputesInWith

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
