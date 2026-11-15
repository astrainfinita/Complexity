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
computing in every interpretation (`ComputesWith`) and within budgets (`ComputesWithinCostWith`),
their transfer along a correspondence of histories (`forall_mem_histories_of_liftRel`,
`ComputesWith.of_liftRel`, together `ComputesWithinCostWith.of_liftRel`) and the deterministic case
`ComputesWithinCost`, halting on an input (`Terminates`, `HaltsAt`), and measurements of these runs.
A lemma belongs here when it is the counterpart, at `M.init input`, of a lemma about runs from an
arbitrary configuration, or when it is about a notion that needs the input and output conventions.

A requirement on a run is stated on its histories alone, `∀ h ∈ M.histories m input, P h`, which
covers every history at every depth. `ComputesWith` is the other half: the run halts and its outputs
are read. They live in the same interpretation as the run: on `Multiset` they are the outputs of all
branches with their multiplicities. `ComputesWithinCostWith` is the conjunction of the requirement
that two measurements stay within budget with `ComputesWith`. The deterministic `ComputesWithinCost`
is the instance on `Id`: the budgets bound the history at every depth, including the halted padding,
and the run halts with the output (`computesWithinCost_iff`). When both measurements are monotone
along the run, the bounds at a halting step are enough (`ComputesWithinCost.of_halted`); each model
specification has its own `of_halted` with the monotonicity filled in. Supplying monotonicity
through one lemma per specification is the current state, not a decision, and so is reading the
budgets at every depth rather than on halted histories only. The output type lives in the universe
of the results, `Type (max u v)`; this is a current limitation, not a decision. The way halting is
stated, inside the correspondence at one step of the run, is the current state too.
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

variable {F : Type (max u v) → Type*} {Input Observation : Type*} {Action : Type u}
  {Config : Input → Type u} {Q : Type v} {Output : Type (max u v)}
  [∀ x, Observe (Config x) Observation] [∀ x, Apply (Config x) Action]

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

/-- Forgetting the histories of a standard-input run recovers the run. -/
@[simp] theorem last_runHistoryWith (m : Type (max u v) → Type*) [Monad m] [LawfulMonad m]
    [MonadLiftT F m] (M : Controller F Observation Action Q) (input : Input) (n : ℕ)
    [HasConfig Action Input Config] :
    History.last <$> M.runHistoryWith m input n = M.runWith m input n :=
  M.last_runHistoryFromWith m (M.init input) n

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
        rw [← M.last_runHistoryWith m, mem_returns_map_iff]; exact ⟨p, hp, rfl⟩)
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
  rw [← M.last_runHistoryWith m, mem_returns_map_iff] at hc
  obtain ⟨h, hh, rfl⟩ := hc
  exact (M.runHistoryFromWith_spec m (M.init input) (t + 1) h hh).stopped.resolve_left
    fun hlen ↦ absurd (hl h ((M.mem_histories_iff m input).2 ⟨t + 1, hh⟩)) (by omega)

end Histories

section ComputesWith

/-- `M` computes `outputs` from `input` in the interpretation `m`: at some step the results of the
run correspond to `outputs` branch by branch, each branch halted with the corresponding output. -/
def ComputesWith (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config]
    [∀ x, HasOutput (Config x) Output] (outputs : m Output) : Prop :=
  ∃ n, LiftRel (fun c y ↦ M.Halted c ∧ HasOutput.IsOutput c.2 y) (M.runWith m input n) outputs

/-- `M` computes `outputs` from `input` in the interpretation `m` within both budgets: on every
history the two measurements are within budget, and `M` computes `outputs`. -/
def ComputesWithinCostWith (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m] [MonadReturns m]
    (M : Controller F Observation Action Q) (input : Input) [HasConfig Action Input Config]
    [∀ x, HasOutput (Config x) Output] (outputs : m Output)
    (timeCost spaceCost : History (Config input) Action → ℕ) (time space : ℕ) : Prop :=
  (∀ h ∈ M.histories m input, timeCost h.snd ≤ time ∧ spaceCost h.snd ≤ space) ∧
    M.ComputesWith m input outputs

/-- The deterministic case of `ComputesWithinCostWith`: on every history of the run, including the
halted padding, the two measurements are within budget, and the run halts with `output`. The
measurements read histories without the control states.

Build it with `ComputesWithinCost.of_halted`, or with the `of_halted` of a model specification, and
take it apart with `ComputesWithinCost.exists_halted`; `computesWithinCost_iff` is its reading on
`Id`. The definition unfolds to the general predicate and is not meant to be opened by hand: an
anonymous constructor or a pattern would meet the two clauses of `ComputesWithinCostWith`, not the
halting step. -/
def ComputesWithinCost (M : Controller Id Observation Action Q) (input : Input)
    [HasConfig Action Input Config] [∀ x, HasOutput (Config x) Output] (output : Output)
    (timeCost spaceCost : History (Config input) Action → ℕ) (time space : ℕ) : Prop :=
  M.ComputesWithinCostWith Id input (pure output) timeCost spaceCost time space

variable {m : Type (max u v) → Type*} [Monad m] [MonadLiftT F m] [MonadReturns m]
  {M : Controller F Observation Action Q} {input : Input} [HasConfig Action Input Config]
  [∀ x, HasOutput (Config x) Output] {outputs : m Output}
  {timeCost spaceCost : History (Config input) Action → ℕ} {time space : ℕ}

/-- Enlarging budgets keeps the same outputs. -/
theorem computesWithinCostWith_mono {time' space' : ℕ}
    (h : M.ComputesWithinCostWith m input outputs timeCost spaceCost time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesWithinCostWith m input outputs timeCost spaceCost time' space' :=
  ⟨fun h' hh ↦ (h.1 h' hh).imp (·.trans ht) (·.trans hs), h.2⟩

section Transfer

variable [LawfulMonad m] {F' : Type (max u v) → Type*} {Input' Observation' : Type*}
  {Action' : Type u} {Config' : Input' → Type u} {Q' : Type v} {Output' : Type (max u v)}
  [∀ x, Observe (Config' x) Observation'] [∀ x, Apply (Config' x) Action'] [MonadLiftT F' m]
  {N : Controller F' Observation' Action' Q'} {input' : Input'} [HasConfig Action' Input' Config']
  [∀ x, HasOutput (Config' x) Output'] {timeCost' spaceCost' : History (Config' input') Action' → ℕ}
  {time' space' : ℕ}
  {S : History (Q × Config input) (Q × Action) →
    History (Q' × Config' input') (Q' × Action') → Prop}

/-- A requirement on the histories passes along a correspondence of histories: when at every depth
the histories of `M` and `N` correspond under `S`, and `S` carries `P` to `P'`, every history of
`N` satisfies `P'`. The machines and the inputs are explicit: when the configuration type depends
on the input they are not inferred from the statement, nor from `hS`. -/
theorem forall_mem_histories_of_liftRel (M : Controller F Observation Action Q) (input : Input)
    (N : Controller F' Observation' Action' Q') (input' : Input')
    {S : History (Q × Config input) (Q × Action) →
      History (Q' × Config' input') (Q' × Action') → Prop}
    {P : History (Q × Config input) (Q × Action) → Prop}
    {P' : History (Q' × Config' input') (Q' × Action') → Prop}
    (hS : ∀ n, LiftRel S (M.runHistoryWith m input n) (N.runHistoryWith m input' n))
    (hP : ∀ p q, S p q → P p → P' q) (h : ∀ p ∈ M.histories m input, P p) :
    ∀ q ∈ N.histories m input', P' q := by
  intro q hq
  obtain ⟨k, hk⟩ := (N.mem_histories_iff m input').1 hq
  obtain ⟨p, hp, hpq⟩ := (hS k).exists_mem_of_mem_right hk
  exact hP p q hpq (h p ((M.mem_histories_iff m input).2 ⟨k, hp⟩))

/-- A computation passes along a correspondence of histories: when at every depth the histories of
`M` and `N` correspond under `S`, and `S` carries halting and the outputs, `N` computes the images
under `g` of the outputs of `M`. The outputs of `M` are given as a function `out` of its
configuration, since two correspondences cannot be composed in an arbitrary interpretation. Apply
it against the expected statement: the second machine and its input are not inferred from `hS`
alone, because the configuration type depends on the input. -/
theorem ComputesWith.of_liftRel {g : Output → Output'} (h : M.ComputesWith m input outputs)
    (hS : ∀ n, LiftRel S (M.runHistoryWith m input n) (N.runHistoryWith m input' n))
    (out : Q × Config input → Output) (hout : ∀ c y, HasOutput.IsOutput c.2 y → y = out c)
    (hh : ∀ p q, S p q → M.Halted p → N.Halted q)
    (ho : ∀ p q y, S p q → HasOutput.IsOutput p.last.2 y → HasOutput.IsOutput q.last.2 (g y)) :
    N.ComputesWith m input' (g <$> outputs) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← last_runHistoryWith] at hn
  rw [hn.eq_map fun c y h ↦ hout c y h.2, ← last_runHistoryWith, Functor.map_map,
    Functor.map_map]
  have h' : LiftRel (fun p q ↦ N.Halted q.last ∧ HasOutput.IsOutput q.last.2 (g (out p.last)))
      (M.runHistoryWith m input n) (N.runHistoryWith m input' n) :=
    (hS n).mono_of_mem fun p hp q hpq ↦
      let ⟨y, _, hH, hy⟩ := hn.exists_mem_of_mem_left (mem_returns_map_iff.2 ⟨p, hp, rfl⟩)
      ⟨hh p q hpq hH, hout _ _ hy ▸ ho p q y hpq hy⟩
  exact (h'.map fun _ _ ↦ id).swap

/-- A computation within budgets passes along a correspondence of histories: the budgets by
`forall_mem_histories_of_liftRel`, the outputs by `ComputesWith.of_liftRel`. Apply it against the
expected statement, as `ComputesWith.of_liftRel`. -/
theorem ComputesWithinCostWith.of_liftRel {g : Output → Output'}
    (h : M.ComputesWithinCostWith m input outputs timeCost spaceCost time space)
    (hS : ∀ n, LiftRel S (M.runHistoryWith m input n) (N.runHistoryWith m input' n))
    (out : Q × Config input → Output) (hout : ∀ c y, HasOutput.IsOutput c.2 y → y = out c)
    (hb : ∀ p q, S p q → timeCost p.snd ≤ time ∧ spaceCost p.snd ≤ space →
      timeCost' q.snd ≤ time' ∧ spaceCost' q.snd ≤ space')
    (hh : ∀ p q, S p q → M.Halted p → N.Halted q)
    (ho : ∀ p q y, S p q → HasOutput.IsOutput p.last.2 y → HasOutput.IsOutput q.last.2 (g y)) :
    N.ComputesWithinCostWith m input' (g <$> outputs) timeCost' spaceCost' time' space' :=
  ⟨M.forall_mem_histories_of_liftRel input N input' hS hb h.1, h.2.of_liftRel hS out hout hh ho⟩

end Transfer

end ComputesWith

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

theorem length_runHistory_mono (input : Input) [HasConfig Action Input Config] {n k : ℕ}
    (h : n ≤ k) : (M.runHistory input n).snd.length ≤ (M.runHistory input k).snd.length := by
  simpa only [History.actionSum_unit] using M.actionSum_runHistory_mono input (fun _ _ ↦ 1) h

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

variable {M : Controller Id Observation Action Q} {input : Input} [HasConfig Action Input Config]
  [∀ x, HasOutput (Config x) Output] {output : Output}
  {timeCost spaceCost : History (Config input) Action → ℕ} {time space : ℕ}

/-- The budgets bound the history at every depth, and the run halts with the output. -/
theorem computesWithinCost_iff :
    M.ComputesWithinCost input output timeCost spaceCost time space ↔
      (∀ k, timeCost (M.runHistory input k).snd ≤ time ∧
        spaceCost (M.runHistory input k).snd ≤ space) ∧
      ∃ n, M.Halted (M.run input n) ∧ HasOutput.IsOutput (M.run input n).2 output := by
  simp only [ComputesWithinCost, ComputesWithinCostWith, ComputesWith,
    M.forall_mem_histories_iff Id input, Id.mem_returns, forall_eq, liftRel_id_iff]
  rfl

/-- When both measurements are monotone along the run, the bounds at a halting step bound every
depth, since the history stays fixed after halting. -/
theorem ComputesWithinCost.of_halted (ht : Monotone fun k ↦ timeCost (M.runHistory input k).snd)
    (hs : Monotone fun k ↦ spaceCost (M.runHistory input k).snd) (n : ℕ)
    (hn : M.Halted (M.run input n)) (ho : HasOutput.IsOutput (M.run input n).2 output)
    (htn : timeCost (M.runHistory input n).snd ≤ time)
    (hsn : spaceCost (M.runHistory input n).snd ≤ space) :
    M.ComputesWithinCost input output timeCost spaceCost time space := by
  refine computesWithinCost_iff.2 ⟨fun k ↦ ?_, n, hn, ho⟩
  rcases le_total k n with hk | hk
  · exact ⟨(ht hk).trans htn, (hs hk).trans hsn⟩
  · rw [M.runHistory_eq_of_halted input hn hk]
    exact ⟨htn, hsn⟩

/-- The halting step of a computation, with the output and both measurements within budget. -/
theorem ComputesWithinCost.exists_halted
    (h : M.ComputesWithinCost input output timeCost spaceCost time space) :
    ∃ n, M.Halted (M.run input n) ∧ HasOutput.IsOutput (M.run input n).2 output ∧
      timeCost (M.runHistory input n).snd ≤ time ∧
      spaceCost (M.runHistory input n).snd ≤ space :=
  let ⟨hb, n, hn, ho⟩ := computesWithinCost_iff.1 h
  ⟨n, hn, ho, hb n⟩

/-- Enlarging budgets keeps the same output. -/
theorem computesWithinCost_mono {time' space' : ℕ}
    (h : M.ComputesWithinCost input output timeCost spaceCost time space)
    (ht : time ≤ time') (hs : space ≤ space') :
    M.ComputesWithinCost input output timeCost spaceCost time' space' :=
  computesWithinCostWith_mono h ht hs

/-- The time budget bounds the history at every depth. -/
theorem computesWithinCost_time_le
    (h : M.ComputesWithinCost input output timeCost spaceCost time space) (k : ℕ) :
    timeCost (M.runHistory input k).snd ≤ time :=
  ((computesWithinCost_iff.1 h).1 k).1

/-- The space budget bounds the history at every depth. -/
theorem computesWithinCost_space_le
    (h : M.ComputesWithinCost input output timeCost spaceCost time space) (k : ℕ) :
    spaceCost (M.runHistory input k).snd ≤ space :=
  ((computesWithinCost_iff.1 h).1 k).2

/-- Counting recorded actions describes the halted run at the advertised time bound. -/
theorem computesWithinCost_unit_iff :
    M.ComputesWithinCost input output History.length spaceCost time space ↔
      M.Halted (M.run input time) ∧ HasOutput.IsOutput (M.run input time).2 output ∧
      ∀ k, spaceCost (M.runHistory input k).snd ≤ space := by
  rw [computesWithinCost_iff]
  constructor
  · rintro ⟨hb, n, hn, ho⟩
    have he : M.run input (M.runHistory input n).length = M.run input n :=
      M.runFrom_length_runHistoryFrom (M.init input) n
    rw [M.run_eq_of_halted input (he ▸ hn) ((History.length_snd _).symm.trans_le (hb n).1), he]
    exact ⟨hn, ho, fun k ↦ (hb k).2⟩
  · rintro ⟨hn, ho, hs⟩
    exact ⟨fun k ↦ ⟨(History.length_snd _).trans_le (M.length_runHistory_le_of_halted input hn k),
      hs k⟩, time, hn, ho⟩

end Complexity.Controller
