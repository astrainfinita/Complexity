/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.RunHistory
public import Complexity.Control.Controller.History.Cost

/-!
# Measurements of controller histories

Action sums and configuration maxima are projections of the same execution history.
Actions are charged at their source configuration. The maximum includes both endpoints.
Halting padding adds neither actions nor configurations.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {F : Type u → Type*} {Observation : Type*} {Action Config : Type u}
  {Q : Type*}

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
  (M.runHistoryFrom cfg n).actionSum cost

@[simp] theorem runActionSumFrom_zero (cfg : Config) : M.runActionSumFrom cost cfg 0 = 0 := by
  simp [runActionSumFrom]

theorem runActionSumFrom_succ (cfg : Config) (n : ℕ) :
    M.runActionSumFrom cost cfg (n + 1) = M.stepCost cost cfg +
      M.runActionSumFrom cost (M.step cfg) n := by
  by_cases h : M.Halted cfg
  · rw [M.step_of_halted cfg h, M.stepCost_of_halted cost cfg h]
    simp [runActionSumFrom, M.runHistoryFrom_of_halted cfg h]
  · rw [M.step_of_not_halted cfg h]
    simp [runActionSumFrom, M.runHistoryFrom_succ_of_not_halted cfg h, stepCost,
      show M.halt (state cfg) ≠ true from h]

theorem runActionSumFrom_add (cfg : Config) (n k : ℕ) :
    M.runActionSumFrom cost cfg (n + k) = M.runActionSumFrom cost cfg n +
      M.runActionSumFrom cost (M.runFrom cfg n) k := by
  simp only [runActionSumFrom, runHistoryFrom_add, History.actionSum_append]
  simp only [← runActionSumFrom.eq_def, last_runHistoryFrom]

theorem runActionSumFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    M.runActionSumFrom cost cfg n ≤ M.runActionSumFrom cost cfg k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [runActionSumFrom_add]
  exact Nat.le_add_right _ _

theorem runActionSumFrom_succ' (cfg : Config) (n : ℕ) :
    M.runActionSumFrom cost cfg (n + 1) = M.runActionSumFrom cost cfg n +
      M.stepCost cost (M.runFrom cfg n) := by
  rw [runActionSumFrom_add, runActionSumFrom_succ, runActionSumFrom_zero, Nat.add_zero]

theorem runActionSumFrom_of_halted (cfg : Config) (h : M.Halted cfg) (n : ℕ) :
    M.runActionSumFrom cost cfg n = 0 := by
  simp [runActionSumFrom, M.runHistoryFrom_of_halted cfg h]

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
  simpa [runActionSumFrom] using (M.runHistoryFrom_spec cfg n).length_le

/-- Removing halting padding by counting unit-cost actions preserves the endpoint. -/
theorem runFrom_runActionSumFrom_unit (cfg : Config) (n : ℕ) :
    M.runFrom cfg (M.runActionSumFrom (fun _ _ => 1) cfg n) = M.runFrom cfg n := by
  simpa only [runActionSumFrom, History.actionSum_unit] using
    M.runFrom_length_runHistoryFrom cfg n

/-- Pointwise larger action charges give a larger total on the same history. -/
theorem runActionSumFrom_mono_cost {cost cost' : Action → Config → ℕ}
    (h : ∀ a c, cost a c ≤ cost' a c) (cfg : Config) (n : ℕ) :
    M.runActionSumFrom cost cfg n ≤ M.runActionSumFrom cost' cfg n :=
  (M.runHistoryFrom cfg n).actionSum_mono h

/-- Unit action charges count every step before the first halt. -/
theorem runActionSumFrom_unit_eq (cfg : Config) (n : ℕ)
    (h : ∀ i < n, ¬M.Halted (M.runFrom cfg i)) :
    M.runActionSumFrom (fun _ _ ↦ 1) cfg n = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [runActionSumFrom_succ', ih (fun i hi ↦ h i (by omega))]
    simp [stepCost, show M.halt (state (M.runFrom cfg n)) ≠ true from h n (by omega)]

end Deterministic

section Space

variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] [Apply Config Action] (space : Config → ℕ)

/-- Maximum configuration space charge through the given number of steps, including time zero. -/
def runConfigMaxFrom (cfg : Config) (n : ℕ) : ℕ :=
  (M.runHistoryFrom cfg n).configSup space

@[simp] theorem runConfigMaxFrom_zero (cfg : Config) :
    M.runConfigMaxFrom space cfg 0 = space cfg := by
  simp [runConfigMaxFrom]

/-- Sequential segments combine their configuration peaks by taking the maximum. -/
theorem runConfigMaxFrom_add (cfg : Config) (n k : ℕ) :
    M.runConfigMaxFrom space cfg (n + k) = max (M.runConfigMaxFrom space cfg n)
      (M.runConfigMaxFrom space (M.runFrom cfg n) k) := by
  simp only [runConfigMaxFrom, runHistoryFrom_add, History.configSup_append]
  simp only [← runConfigMaxFrom.eq_def, last_runHistoryFrom]

theorem runConfigMaxFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    M.runConfigMaxFrom space cfg n ≤ M.runConfigMaxFrom space cfg k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [runConfigMaxFrom_add]
  exact le_max_left _ _

/-- The peak bounds each configuration, including the initial and final ones. -/
theorem space_le_runConfigMaxFrom (cfg : Config) {i n : ℕ} (h : i ≤ n) :
    space (M.runFrom cfg i) ≤ M.runConfigMaxFrom space cfg n :=
  (M.runHistoryFrom cfg n).config_le_configSup space
    ((M.mem_configs_runHistoryFrom cfg n _).mpr ⟨i, h, rfl⟩)

theorem runConfigMaxFrom_le_iff (cfg : Config) (n bound : ℕ) :
    M.runConfigMaxFrom space cfg n ≤ bound ↔
      ∀ i ≤ n, space (M.runFrom cfg i) ≤ bound := by
  simp only [runConfigMaxFrom, History.configSup_le_iff, mem_configs_runHistoryFrom,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- Extending a run retains the previous peak and includes the new endpoint. -/
theorem runConfigMaxFrom_succ (cfg : Config) (n : ℕ) :
    M.runConfigMaxFrom space cfg (n + 1) = max (M.runConfigMaxFrom space cfg n)
      (space (M.runFrom cfg (n + 1))) := by
  apply eq_of_forall_ge_iff
  intro bound
  simp only [runConfigMaxFrom_le_iff, max_le_iff, Nat.le_succ_iff, or_imp,
    forall_and, forall_eq]

theorem runConfigMaxFrom_of_halted (cfg : Config) (h : M.Halted cfg) (n : ℕ) :
    M.runConfigMaxFrom space cfg n = space cfg := by
  simp [runConfigMaxFrom, M.runHistoryFrom_of_halted cfg h]

/-- Once a run halts, padding preserves its peak space rather than only its final space. -/
theorem runConfigMaxFrom_eq_of_halted (cfg : Config) {n k : ℕ}
    (h : M.Halted (Config := Config) (M.runFrom cfg n))
    (hk : n ≤ k) :
    M.runConfigMaxFrom space cfg k = M.runConfigMaxFrom space cfg n := by
  simp only [runConfigMaxFrom, M.runHistoryFrom_eq_of_halted cfg h hk]

end Space
end Complexity.Controller
