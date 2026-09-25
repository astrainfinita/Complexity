/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller
public import Complexity.Control.Transition.Cost
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Controllers with external action costs

Costs are charged when an action is selected, so different actions with the same
successor configuration can still have different charges. Each interpreted branch
retains its own cumulative cost. Halting padding selects no action and costs zero.
For deterministic controllers, the cumulative cost also uses `Transition.runCost`.
Space is the maximum configuration space charge along the run, including both endpoints.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {F : Type u → Type*} {Observation : Type*} {Action Config : Type u}
  {Q : Type*}

section Execution

variable (m : Type u → Type*) [Monad m] [MonadLiftT F m]
variable [HasState Config Q] [Observe Config Observation] [Apply Config Action]

/-- Execute one interpreted action together with its external charge. -/
def stepWithCost (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) : m (Config × ℕ) :=
  if M.halt (state cfg) then pure (cfg, 0)
  else (fun action ↦ (apply action cfg, cost action cfg)) <$>
    monadLift (M.transition (state cfg) (observe cfg))

theorem stepWithCost_of_halted (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) (h : M.Halted cfg) :
    M.stepWithCost m cost cfg = pure (cfg, 0) := by
  simp [stepWithCost, show M.halt (state cfg) = true from h]

/-- Run a controller and sum the charges along each interpreted branch. -/
def runFromWithCost (m : Type u → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) : ℕ → m (Config × ℕ)
  | 0 => pure (cfg, 0)
  | n + 1 => do
    let next ← M.stepWithCost m cost cfg
    let rest ← M.runFromWithCost m cost next.1 n
    pure (rest.1, next.2 + rest.2)

@[simp] theorem runFromWithCost_zero (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) :
    M.runFromWithCost m cost cfg 0 = pure (cfg, 0) := rfl

section Lawful

variable [LawfulMonad m]

/-- Charging an action does not change its successor configuration. -/
@[simp] theorem fst_stepWithCost (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) :
    Prod.fst <$> M.stepWithCost m cost cfg = M.stepWith m cfg := by
  by_cases h : M.halt (state cfg) = true <;>
    simp [stepWithCost, stepWith, h, Functor.map_map]

/-- Forgetting charges recovers the original interpreted execution. -/
@[simp] theorem fst_runFromWithCost (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) (n : ℕ) :
    Prod.fst <$> M.runFromWithCost m cost cfg n =
      M.runFromWith m cfg n := by
  induction n generalizing cfg with
  | zero => simp [runFromWithCost, runFromWith]
  | succ n ih =>
    simp only [runFromWithCost, runFromWith_succ, map_bind, map_pure]
    simp_rw [← map_eq_pure_bind, ih]
    rw [← M.fst_stepWithCost m cost cfg]
    simp only [bind_map_left]

theorem runFromWithCost_of_halted (M : Controller F Observation Action Q)
    (cost : Action → Config → ℕ)
    (cfg : Config) (h : M.Halted cfg)
    (n : ℕ) : M.runFromWithCost m cost cfg n = pure (cfg, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runFromWithCost, M.stepWithCost_of_halted m cost cfg h, ih]

end Lawful
end Execution

section StepCost

variable {Action Config : Type*}
variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] (cost : Action → Config → ℕ)

/-- Charge the action selected by a deterministic controller, or zero after halting. -/
def stepCost (cfg : Config) : ℕ :=
  if M.halt (state cfg) then 0
  else cost ((M.transition (state cfg) (observe cfg)).run) cfg

theorem stepCost_of_halted (cfg : Config) (h : M.Halted cfg) :
    M.stepCost cost cfg = 0 := by
  simp [stepCost, show M.halt (state cfg) = true from h]

end StepCost

section Deterministic

variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] [Apply Config Action]
  (cost : Action → Config → ℕ)

/-- Accumulate action charges along deterministic execution. -/
def runActionSumFrom (cfg : Config) (n : ℕ) : ℕ :=
  Transition.runCost M.step
    (fun current _ ↦ M.stepCost cost current) n cfg

@[simp] theorem runActionSumFrom_zero (cfg : Config) : M.runActionSumFrom cost cfg 0 = 0 := rfl

theorem runActionSumFrom_succ (cfg : Config) (n : ℕ) :
    M.runActionSumFrom cost cfg (n + 1) = M.stepCost cost cfg +
      M.runActionSumFrom cost (M.step cfg) n := rfl

theorem runActionSumFrom_add (cfg : Config) (n k : ℕ) :
    M.runActionSumFrom cost cfg (n + k) = M.runActionSumFrom cost cfg n +
      M.runActionSumFrom cost (M.runFrom cfg n) k :=
  Transition.runCost_add _ _ _ _ _

theorem runActionSumFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    M.runActionSumFrom cost cfg n ≤ M.runActionSumFrom cost cfg k :=
  Transition.runCost_mono _ _ _ h

@[simp] theorem snd_stepWithCost (cfg : Config) :
    ((M.stepWithCost Id cost cfg).run).snd =
      M.stepCost cost cfg := by
  by_cases h : M.halt (state cfg) = true <;>
    simp [stepWithCost, stepCost, h]

/-- The branch-aware runner and the deterministic cost accumulator agree. -/
@[simp] theorem snd_runFromWithCost (cfg : Config) (n : ℕ) :
    ((M.runFromWithCost Id cost cfg n).run).snd =
      M.runActionSumFrom cost cfg n := by
  induction n generalizing cfg with
  | zero => rfl
  | succ n ih =>
    change ((M.stepWithCost Id cost cfg).run).snd +
      ((M.runFromWithCost Id cost
        ((M.stepWithCost Id cost cfg).run).fst n).run).snd = _
    rw [ih, snd_stepWithCost, runActionSumFrom_succ]
    congr 1
    exact congrArg (fun c ↦ M.runActionSumFrom cost c.run n)
      (M.fst_stepWithCost Id cost cfg)

theorem runActionSumFrom_of_halted (cfg : Config) (h : M.Halted cfg) (n : ℕ) :
    M.runActionSumFrom cost cfg n = 0 := by
  rw [← M.snd_runFromWithCost cost, M.runFromWithCost_of_halted Id cost cfg h n]
  rfl

/-- Padding a run after its halting point does not add action charges. -/
theorem runActionSumFrom_eq_of_halted (cfg : Config) {n k : ℕ}
    (h : M.Halted (Config := Config) (M.runFrom cfg n))
    (hk : n ≤ k) :
    M.runActionSumFrom cost cfg k = M.runActionSumFrom cost cfg n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [runActionSumFrom_add, M.runActionSumFrom_of_halted cost _ h, Nat.add_zero]

/-- Unit charges count at most one executed action per padded transition. -/
theorem runActionSumFrom_unit_le (cfg : Config) (n : ℕ) :
    M.runActionSumFrom (fun _ _ => 1) cfg n ≤ n := by
  induction n generalizing cfg with
  | zero => exact le_rfl
  | succ n ih =>
    rw [runActionSumFrom_succ]
    have hstep : M.stepCost (fun _ _ => 1) cfg ≤ 1 := by
      simp only [stepCost]
      split <;> omega
    exact (Nat.add_le_add hstep (ih _)).trans (by omega)

/-- Removing halting padding by counting unit-cost actions preserves the endpoint. -/
theorem runFrom_runActionSumFrom_unit (cfg : Config) (n : ℕ) :
    M.runFrom cfg (M.runActionSumFrom (fun _ _ => 1) cfg n) = M.runFrom cfg n := by
  induction n generalizing cfg with
  | zero => rfl
  | succ n ih =>
    by_cases h : M.Halted cfg
    · rw [M.runActionSumFrom_of_halted (fun _ _ => 1) cfg h,
        M.runFrom_of_halted cfg h,
        M.runFrom_of_halted cfg h]
    · have hstep : M.stepCost (fun _ _ => 1) cfg = 1 := by
        simp [stepCost, show M.halt (state cfg) ≠ true from h]
      rw [runActionSumFrom_succ, hstep, Nat.add_comm 1, runFrom_succ, runFrom_succ]
      exact ih _

end Deterministic

section Space

variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] [Apply Config Action] (space : Config → ℕ)

/-- Maximum configuration space charge through the given number of steps, including time zero. -/
def runConfigMaxFrom (cfg : Config) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun i ↦
    space (M.runFrom cfg i)

@[simp] theorem runConfigMaxFrom_zero (cfg : Config) :
    M.runConfigMaxFrom space cfg 0 = space cfg := by
  simp only [runConfigMaxFrom, Nat.zero_add, Finset.range_one, Finset.sup_singleton]
  rfl

/-- Extending a run retains the previous peak and includes the new endpoint. -/
theorem runConfigMaxFrom_succ (cfg : Config) (n : ℕ) :
    M.runConfigMaxFrom space cfg (n + 1) = max (M.runConfigMaxFrom space cfg n)
      (space (M.runFrom cfg (n + 1))) := by
  simp only [runConfigMaxFrom, Finset.range_add_one, Finset.sup_insert]
  exact max_comm _ _

theorem runConfigMaxFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    M.runConfigMaxFrom space cfg n ≤ M.runConfigMaxFrom space cfg k :=
  Finset.sup_mono (Finset.range_mono (by omega))

/-- The peak bounds each configuration, including the initial and final ones. -/
theorem space_le_runConfigMaxFrom (cfg : Config) {i n : ℕ} (h : i ≤ n) :
    space (M.runFrom cfg i) ≤
      M.runConfigMaxFrom space cfg n :=
  Finset.le_sup (f := fun j ↦ space (M.runFrom cfg j))
    (Finset.mem_range.mpr (by omega))

theorem runConfigMaxFrom_le_iff (cfg : Config) (n bound : ℕ) :
    M.runConfigMaxFrom space cfg n ≤ bound ↔
      ∀ i ≤ n, space (M.runFrom cfg i) ≤ bound := by
  constructor
  · intro h i hi
    exact (M.space_le_runConfigMaxFrom space cfg hi).trans h
  · intro h
    exact Finset.sup_le fun i hi ↦ h i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)

theorem runConfigMaxFrom_of_halted (cfg : Config) (h : M.Halted cfg) (n : ℕ) :
    M.runConfigMaxFrom space cfg n = space cfg := by
  apply Nat.le_antisymm
  · apply (M.runConfigMaxFrom_le_iff space cfg n _).2
    intro i _
    rw [M.runFrom_of_halted cfg h i]
  · exact M.space_le_runConfigMaxFrom space cfg (Nat.zero_le n)

/-- Once a run halts, padding preserves its peak space rather than only its final space. -/
theorem runConfigMaxFrom_eq_of_halted (cfg : Config) {n k : ℕ}
    (h : M.Halted (Config := Config) (M.runFrom cfg n))
    (hk : n ≤ k) :
    M.runConfigMaxFrom space cfg k = M.runConfigMaxFrom space cfg n := by
  apply Nat.le_antisymm ?_ (M.runConfigMaxFrom_mono space cfg hk)
  apply (M.runConfigMaxFrom_le_iff space cfg k _).2
  intro i _
  by_cases hi : i ≤ n
  · exact M.space_le_runConfigMaxFrom space cfg hi
  · have hn : n ≤ i := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have he : M.runFrom cfg (n + j) =
        M.runFrom cfg n := by
      rw [M.runFrom_add]
      exact M.runFrom_of_halted _ h j
    rw [he]
    exact M.space_le_runConfigMaxFrom space cfg (Nat.le_refl n)

end Space
end Complexity.Controller
