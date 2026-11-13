/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.History.Basic

/-! # Bounded execution histories

A run records only selected actions. It stops when its fuel is exhausted or its controller
halts, preserving the interpreted choices in the target monad.
-/

@[expose] public section

universe u v

namespace Complexity.Controller

variable {F : Type (max u v) → Type*} {Observation : Type*} {Action : Type u} {Q : Type v}
  {Config : Type (max u v)} [HasState Config Q] [Apply Config (Q × Action)]

/-- Endpoint and stopping conditions for a bounded run. These conditions alone do not require
that the actions come from the controller's transition function. -/
structure RunConditions (M : Controller F Observation Action Q) (start : Config) (fuel : ℕ)
    (h : History Config (Q × Action)) : Prop where
  first_eq : h.first = start
  length_le : h.length ≤ fuel
  stopped : h.length = fuel ∨ M.Halted h.last
  active : ∀ c ∈ h.configs.dropLast, ¬M.Halted c

namespace RunConditions

variable (M : Controller F Observation Action Q)

/-- No action is performed without fuel. -/
theorem nil (cfg : Config) : M.RunConditions cfg 0 (History.nil cfg) where
  first_eq := rfl
  length_le := le_rfl
  stopped := Or.inl rfl
  active c hc := by simp at hc

/-- A halted history stays unchanged with one more unit of fuel. -/
theorem of_halted {cfg : Config} {fuel : ℕ} {h : History Config (Q × Action)}
    (hr : M.RunConditions cfg fuel h) (hh : M.Halted h.last) :
    M.RunConditions cfg (fuel + 1) h where
  first_eq := hr.first_eq
  length_le := hr.length_le.trans (Nat.le_succ _)
  stopped := Or.inr hh
  active := hr.active

/-- An action at an active last configuration extends the history with one more unit of fuel. -/
theorem snoc {cfg : Config} {fuel : ℕ} {h : History Config (Q × Action)}
    (hr : M.RunConditions cfg fuel h) (hh : ¬M.Halted h.last) (a : Q × Action) :
    M.RunConditions cfg (fuel + 1) (h.snoc a) where
  first_eq := hr.first_eq
  length_le := by simpa using hr.length_le
  stopped := Or.inl (by rw [History.snoc_length, hr.stopped.resolve_right hh])
  active c hc := by
    rw [History.configs_snoc, List.dropLast_concat,
      ← List.dropLast_append_getLast h.configs_ne_nil] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hr.active c hc
    · rw [List.mem_singleton.mp hc]
      simpa only [History.configs, History.last, List.getLast_scanl] using hh

end RunConditions

variable [Observe Config Observation]

/-- Run for at most the supplied fuel, recording the selected actions: the execution on the
history itself, starting from the history with no actions. -/
def runHistoryFromWith (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q) (cfg : Config) (fuel : ℕ) :
    m (History Config (Q × Action)) :=
  M.runFromWith m (History.nil cfg) fuel

section Interpreted

variable (m : Type (max u v) → Type*) [Monad m] [MonadLiftT F m]
  (M : Controller F Observation Action Q)

@[simp] theorem runHistoryFromWith_zero (cfg : Config) :
    M.runHistoryFromWith m cfg 0 = pure (History.nil cfg) := rfl

@[simp] theorem runFromWith_nil (c : Config) (n : ℕ) :
    M.runFromWith m (History.nil (Action := Q × Action) c) n =
      M.runHistoryFromWith m c n := rfl

variable [LawfulMonad m]

/-- Every history a run can return satisfies the common bounded-run conditions. -/
theorem runHistoryFromWith_spec [MonadReturns m] (cfg : Config) (fuel : ℕ) :
    ∀ h ∈ returns (M.runHistoryFromWith m cfg fuel), M.RunConditions cfg fuel h := by
  refine Transition.forall_mem_runN (M.stepWith m) (P := fun k h ↦ M.RunConditions cfg k h)
    (RunConditions.nil M cfg) (fun k h hr h' hh' ↦ ?_) fuel
  by_cases hh : M.Halted h
  · rw [M.stepWith_of_halted m h hh, mem_returns_pure_iff] at hh'
    exact hh' ▸ hr.of_halted M hh
  · rw [M.stepWith_of_not_halted m h hh, mem_returns_map_iff] at hh'
    obtain ⟨a, -, rfl⟩ := hh'
    exact hr.snoc M hh a

@[simp] theorem runHistoryFromWith_of_halted (cfg : Config) (h : M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFromWith m cfg fuel = pure (History.nil cfg) :=
  M.runFromWith_of_halted m (History.nil (Action := Q × Action) cfg) h fuel

/-- Continuing an existing history appends the newly selected actions. -/
private theorem runFromWith_history (p : History Config (Q × Action)) (n : ℕ) :
    M.runFromWith m p n =
      (fun h ↦ (⟨p.first, p.actions ++ h.actions⟩ : History Config (Q × Action))) <$>
        M.runHistoryFromWith m p.last n := by
  induction n generalizing p with
  | zero => simp [runHistoryFromWith]
  | succ n ih =>
    by_cases h : M.Halted p.last
    · rw [M.runFromWith_of_halted m p h, M.runHistoryFromWith_of_halted m p.last h]
      simp
    · rw [runFromWith_succ, runHistoryFromWith, runFromWith_succ,
        M.stepWith_of_not_halted m p h,
        M.stepWith_of_not_halted m (History.nil (Action := Q × Action) p.last) h]
      simp only [History.state_def, History.observe_def, History.last_nil, bind_map_left,
        map_bind]
      congr 1
      funext a
      rw [ih, ih]
      simp [Functor.map_map, History.apply_def]

@[simp] theorem last_runFromWith (p : History Config (Q × Action)) (n : ℕ) :
    History.last <$> M.runFromWith m p n = M.runFromWith m p.last n := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    by_cases h : M.Halted p.last
    · simp [M.runFromWith_of_halted m p h, M.runFromWith_of_halted m p.last h]
    · rw [runFromWith_succ, runFromWith_succ,
        M.stepWith_of_not_halted m p h, M.stepWith_of_not_halted m p.last h]
      simp only [History.state_def, History.observe_def, bind_map_left, map_bind, ih,
        History.apply_last]

/-- Forgetting the history recovers the original padded execution. -/
@[simp] theorem last_runHistoryFromWith (cfg : Config) (fuel : ℕ) :
    History.last <$> M.runHistoryFromWith m cfg fuel = M.runFromWith m cfg fuel :=
  M.last_runFromWith m _ fuel

/-- Splitting the fuel continues the first segment with its existing history. -/
theorem runHistoryFromWith_add (cfg : Config) (n k : ℕ) :
    M.runHistoryFromWith m cfg (n + k) = (do
      let p ← M.runHistoryFromWith m cfg n
      M.runFromWith m p k) :=
  M.runFromWith_add m _ n k

end Interpreted

section Deterministic

variable (M : Controller Id Observation Action Q)

/-- The complete action history of deterministic bounded execution. -/
def runHistoryFrom (cfg : Config) (fuel : ℕ) : History Config (Q × Action) :=
  (M.runHistoryFromWith Id cfg fuel).run

theorem runHistoryFrom_spec (cfg : Config) (fuel : ℕ) :
    M.RunConditions cfg fuel (M.runHistoryFrom cfg fuel) :=
  M.runHistoryFromWith_spec Id cfg fuel _ rfl

@[simp] theorem first_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    (M.runHistoryFrom cfg fuel).first = cfg := (M.runHistoryFrom_spec cfg fuel).first_eq

@[simp] theorem runHistoryFrom_zero (cfg : Config) :
    M.runHistoryFrom cfg 0 = History.nil cfg := rfl

/-- A run records at most one action per unit of fuel. -/
theorem length_runHistoryFrom_le (cfg : Config) (fuel : ℕ) :
    (M.runHistoryFrom cfg fuel).length ≤ fuel := (M.runHistoryFrom_spec cfg fuel).length_le

@[simp] theorem runHistoryFrom_of_halted (cfg : Config) (h : M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFrom cfg fuel = History.nil cfg :=
  congrArg Id.run (M.runHistoryFromWith_of_halted Id cfg h fuel)

@[simp] theorem last_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    (M.runHistoryFrom cfg fuel).last = M.runFrom cfg fuel :=
  congrArg Id.run (M.last_runHistoryFromWith Id cfg fuel)

/-- Continuing an existing history appends the newly selected actions. -/
theorem runFrom_history (p : History Config (Q × Action)) (n : ℕ) :
    M.runFrom p n = p.append (M.runHistoryFrom p.last n)
      (M.first_runHistoryFrom p.last n).symm :=
  congrArg Id.run (M.runFromWith_history Id p n)

@[simp] theorem runFrom_nil (c : Config) (n : ℕ) :
    M.runFrom (History.nil (Action := Q × Action) c) n = M.runHistoryFrom c n := rfl

theorem runHistoryFrom_succ_of_not_halted (cfg : Config) (h : ¬M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFrom cfg (fuel + 1) =
      History.cons cfg (M.transition (state cfg) (observe cfg)).run
        (M.runHistoryFrom (apply (M.transition (state cfg) (observe cfg)).run cfg) fuel)
        (M.first_runHistoryFrom _ _) := by
  have hs := M.runFrom_succ (History.nil (Action := Q × Action) cfg) fuel
  rw [M.step_of_not_halted (History.nil (Action := Q × Action) cfg) h] at hs
  conv_rhs at hs => rw [runFrom_history]
  refine hs.trans ?_
  ext <;> simp [History.apply_def]

/-- Deterministic histories compose at the intermediate configuration. -/
theorem runHistoryFrom_add (cfg : Config) (n k : ℕ) :
    M.runHistoryFrom cfg (n + k) =
      let p := M.runHistoryFrom cfg n
      p.append (M.runHistoryFrom p.last k) (M.first_runHistoryFrom _ _).symm := by
  rw [runHistoryFrom, M.runHistoryFromWith_add Id]
  exact M.runFrom_history _ _

/-- More fuel after halting preserves the complete recorded history. -/
theorem runHistoryFrom_eq_of_halted (cfg : Config) {n k : ℕ}
    (h : M.Halted (M.runFrom cfg n)) (hn : n ≤ k) :
    M.runHistoryFrom cfg k = M.runHistoryFrom cfg n :=
  M.runFrom_eq_of_halted (History.nil (Action := Q × Action) cfg) (by simpa using h) hn

/-- Running for the actual action count reaches the same endpoint as the supplied fuel. -/
theorem runFrom_length_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    M.runFrom cfg (M.runHistoryFrom cfg fuel).length = M.runFrom cfg fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    by_cases h : M.Halted cfg
    · simp [M.runHistoryFrom_of_halted cfg h, M.runFrom_of_halted cfg h]
    · rw [M.runHistoryFrom_succ_of_not_halted cfg h,
        History.cons_length, M.runFrom_succ, M.runFrom_succ]
      rw [M.step_of_not_halted cfg h, ih]

/-- Before the first halt, the action count equals the supplied fuel. -/
theorem length_runHistoryFrom_eq (cfg : Config) (n : ℕ)
    (h : ∀ i < n, ¬M.Halted (M.runFrom cfg i)) :
    (M.runHistoryFrom cfg n).length = n := by
  have hr := M.runHistoryFrom_spec cfg n
  refine hr.stopped.elim id fun hh ↦ le_antisymm hr.length_le (le_of_not_gt fun hlt ↦ ?_)
  exact h _ hlt (by simpa only [M.runFrom_length_runHistoryFrom, ← M.last_runHistoryFrom] using hh)

/-- Recorded configurations are exactly the states reached within the supplied fuel. -/
theorem mem_configs_runHistoryFrom (cfg : Config) (fuel : ℕ) (c : Config) :
    c ∈ (M.runHistoryFrom cfg fuel).configs ↔ ∃ i ≤ fuel, M.runFrom cfg i = c := by
  induction fuel generalizing cfg with
  | zero => simp [eq_comm]
  | succ fuel ih =>
    by_cases h : M.Halted cfg
    · simp [M.runHistoryFrom_of_halted cfg h, M.runFrom_of_halted cfg h,
        show ∃ i : ℕ, i ≤ fuel + 1 from ⟨0, Nat.zero_le _⟩, eq_comm]
    · rw [M.runHistoryFrom_succ_of_not_halted cfg h, History.configs_cons, List.mem_cons, ih]
      conv_rhs => simp only [← Nat.lt_succ_iff]; rw [Nat.exists_lt_succ_left]
      simp only [Nat.lt_succ_iff, runFrom_zero, M.runFrom_succ,
        M.step_of_not_halted cfg h, eq_comm]

end Deterministic

section Prod

variable {C : Type u} [Observe C Observation] [Apply C Action]
  (M : Controller Id Observation Action Q)

/-- Running on a history without control states records the run with its states dropped. -/
theorem runFrom_snd (h : History (Q × C) (Q × Action)) (n : ℕ) :
    M.runFrom (h.last.1, h.snd) n =
      ((M.runFrom h n).last.1, (M.runFrom h n).snd) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, runFrom_succ, ← ih]
    congr 1
    by_cases hh : M.halt h.last.1
    · rw [M.step_of_halted (h.last.1, h.snd) hh, M.step_of_halted h hh]
    · rw [M.step_of_not_halted (h.last.1, h.snd) hh,
        M.step_of_not_halted h hh]
      simp [History.snd, History.last_map]

/-- Starting from an empty history without control states records the run history with its
states dropped. -/
@[simp] theorem runFrom_prod_nil (q : Q) (c : C) (n : ℕ) :
    M.runFrom (q, History.nil (Action := Action) c) n =
      ((M.runFrom (q, c) n).1, (M.runHistoryFrom (q, c) n).snd) := by
  simpa [History.snd] using M.runFrom_snd (History.nil (Action := Q × Action) (q, c)) n

end Prod

end Complexity.Controller
