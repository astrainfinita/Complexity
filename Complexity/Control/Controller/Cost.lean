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

Action sums and configuration suprema are projections of the same execution history. They read
the history without its control states: a measurement depends only on the actions and the
configurations they update. Actions are charged at their source configuration. Configuration
suprema include both endpoints. Halting padding adds neither actions nor configurations.
-/

@[expose] public section

universe u v

namespace Complexity.Controller

variable {F : Type (max u v) → Type*} {Observation : Type*} {Action : Type u} {Q : Type v}
  {Config : Type u} [Observe Config Observation] [Apply Config Action]

section Deterministic

variable (M : Controller Id Observation Action Q) (cost : Action → Config → ℕ)

/-- A one-step history charges the selected action, or zero if the machine has halted. -/
theorem actionSum_runHistoryFrom_one (c : Q × Config) :
    (M.runHistoryFrom c 1).snd.actionSum cost =
      if M.halt c.1 then 0 else cost (M.transition c.1 (observe c.2)).run.2 c.2 := by
  by_cases h : M.Halted c
  · simp [M.runHistoryFrom_of_halted c h, show M.halt c.1 = true from h]
  · simp [M.runHistoryFrom_succ_of_not_halted c h, History.actionSum_snd,
      show M.halt c.1 ≠ true from h]

theorem actionSum_runHistoryFrom_add (c : Q × Config) (n k : ℕ) :
    (M.runHistoryFrom c (n + k)).snd.actionSum cost =
      (M.runHistoryFrom c n).snd.actionSum cost +
        (M.runHistoryFrom (M.runFrom c n) k).snd.actionSum cost := by
  simp only [History.actionSum_snd, runHistoryFrom_add, History.actionSum_append,
    last_runHistoryFrom]

theorem actionSum_runHistoryFrom_mono (c : Q × Config) {n k : ℕ} (h : n ≤ k) :
    (M.runHistoryFrom c n).snd.actionSum cost ≤
      (M.runHistoryFrom c k).snd.actionSum cost := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [actionSum_runHistoryFrom_add]
  exact Nat.le_add_right _ _

end Deterministic

section ConfigSup

variable (M : Controller Id Observation Action Q) {α : Type*} [SemilatticeSup α]
  (space : Config → α)

/-- Sequential segments combine their configuration measurements by taking the supremum. -/
theorem configSup_runHistoryFrom_add (c : Q × Config) (n k : ℕ) :
    (M.runHistoryFrom c (n + k)).snd.configSup space =
      (M.runHistoryFrom c n).snd.configSup space ⊔
        (M.runHistoryFrom (M.runFrom c n) k).snd.configSup space := by
  simp only [History.configSup_snd, runHistoryFrom_add, History.configSup_append,
    last_runHistoryFrom]

theorem configSup_runHistoryFrom_mono (c : Q × Config) {n k : ℕ} (h : n ≤ k) :
    (M.runHistoryFrom c n).snd.configSup space ≤
      (M.runHistoryFrom c k).snd.configSup space := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [configSup_runHistoryFrom_add]
  exact le_sup_left

theorem configSup_runHistoryFrom_le_iff (c : Q × Config) (n : ℕ) (bound : α) :
    (M.runHistoryFrom c n).snd.configSup space ≤ bound ↔
      ∀ i ≤ n, space (M.runFrom c i).2 ≤ bound := by
  simp only [History.configSup_le_iff, History.configs_snd, List.mem_map,
    mem_configs_runHistoryFrom, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- The supremum bounds each configuration measurement, including both endpoints. -/
theorem config_le_configSup_runHistoryFrom (c : Q × Config) {i n : ℕ} (h : i ≤ n) :
    space (M.runFrom c i).2 ≤ (M.runHistoryFrom c n).snd.configSup space :=
  (M.configSup_runHistoryFrom_le_iff space c n _).mp le_rfl i h

/-- Extending a run retains the previous supremum and includes the new endpoint. -/
theorem configSup_runHistoryFrom_succ (c : Q × Config) (n : ℕ) :
    (M.runHistoryFrom c (n + 1)).snd.configSup space =
      (M.runHistoryFrom c n).snd.configSup space ⊔
        space (M.runFrom c (n + 1)).2 := by
  apply eq_of_forall_ge_iff
  intro bound
  simp only [configSup_runHistoryFrom_le_iff, sup_le_iff, Nat.le_succ_iff, or_imp,
    forall_and, forall_eq]

end ConfigSup
end Complexity.Controller
