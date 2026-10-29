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

Action sums and configuration suprema are projections of the same execution history.
Actions are charged at their source configuration. Configuration suprema include both endpoints.
Halting padding adds neither actions nor configurations.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {F : Type u → Type*} {Observation : Type*} {Action Config : Type u}
  {Q : Type*}

section Deterministic

variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] [Apply Config Action]
  (cost : Action → Config → ℕ)

/-- A one-step history charges the selected action, or zero if the machine has halted. -/
theorem actionSum_runHistoryFrom_one (cfg : Config) :
    (M.runHistoryFrom cfg 1).actionSum cost =
      if M.halt (state cfg) then 0
      else cost (M.transition (state cfg) (observe cfg)).run cfg := by
  by_cases h : M.Halted cfg
  · simp [M.runHistoryFrom_of_halted cfg h, show M.halt (state cfg) = true from h]
  · simp [M.runHistoryFrom_succ_of_not_halted cfg h,
      show M.halt (state cfg) ≠ true from h]

theorem actionSum_runHistoryFrom_add (cfg : Config) (n k : ℕ) :
    (M.runHistoryFrom cfg (n + k)).actionSum cost =
      (M.runHistoryFrom cfg n).actionSum cost +
        (M.runHistoryFrom (M.runFrom cfg n) k).actionSum cost := by
  simp only [runHistoryFrom_add, History.actionSum_append, last_runHistoryFrom]

theorem actionSum_runHistoryFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    (M.runHistoryFrom cfg n).actionSum cost ≤ (M.runHistoryFrom cfg k).actionSum cost := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [actionSum_runHistoryFrom_add]
  exact Nat.le_add_right _ _

end Deterministic

section ConfigSup

variable (M : Controller Id Observation Action Q)
  [HasState Config Q] [Observe Config Observation] [Apply Config Action]
  {α : Type*} [SemilatticeSup α] (space : Config → α)

/-- Sequential segments combine their configuration measurements by taking the supremum. -/
theorem configSup_runHistoryFrom_add (cfg : Config) (n k : ℕ) :
    (M.runHistoryFrom cfg (n + k)).configSup space =
      (M.runHistoryFrom cfg n).configSup space ⊔
        (M.runHistoryFrom (M.runFrom cfg n) k).configSup space := by
  simp only [runHistoryFrom_add, History.configSup_append, last_runHistoryFrom]

theorem configSup_runHistoryFrom_mono (cfg : Config) {n k : ℕ} (h : n ≤ k) :
    (M.runHistoryFrom cfg n).configSup space ≤ (M.runHistoryFrom cfg k).configSup space := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [configSup_runHistoryFrom_add]
  exact le_sup_left

/-- The supremum bounds each configuration measurement, including both endpoints. -/
theorem config_le_configSup_runHistoryFrom (cfg : Config) {i n : ℕ} (h : i ≤ n) :
    space (M.runFrom cfg i) ≤ (M.runHistoryFrom cfg n).configSup space :=
  (M.runHistoryFrom cfg n).config_le_configSup space
    ((M.mem_configs_runHistoryFrom cfg n _).mpr ⟨i, h, rfl⟩)

theorem configSup_runHistoryFrom_le_iff (cfg : Config) (n : ℕ) (bound : α) :
    (M.runHistoryFrom cfg n).configSup space ≤ bound ↔
      ∀ i ≤ n, space (M.runFrom cfg i) ≤ bound := by
  simp only [History.configSup_le_iff, mem_configs_runHistoryFrom,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- Extending a run retains the previous supremum and includes the new endpoint. -/
theorem configSup_runHistoryFrom_succ (cfg : Config) (n : ℕ) :
    (M.runHistoryFrom cfg (n + 1)).configSup space =
      (M.runHistoryFrom cfg n).configSup space ⊔ space (M.runFrom cfg (n + 1)) := by
  apply eq_of_forall_ge_iff
  intro bound
  simp only [configSup_runHistoryFrom_le_iff, sup_le_iff, Nat.le_succ_iff, or_imp,
    forall_and, forall_eq]

end ConfigSup
end Complexity.Controller
