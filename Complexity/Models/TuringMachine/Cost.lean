/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Basic
public import Complexity.Models.TuringMachine.History
public import Complexity.Control.Controller.Cost

/-! # Time and visited-cell space of Turing-machine histories -/

@[expose] public section

namespace Complexity.TM

open Controller (History)

variable {κ Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Extending a run can only enlarge its visited intervals. -/
theorem runHistoryFrom_visited_mono (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).snd.visited := fun _ _ h ↦ by
  simpa only [History.visited, History.configSup_snd] using
    M.configSup_runHistoryFrom_mono _ c h

theorem runHistoryFrom_space_mono [Fintype κ] (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).snd.space :=
  fun _ _ h ↦ History.space_mono (M.runHistoryFrom_visited_mono c h)

/-- An interval bounds a tape's visits exactly when it contains every bounded-run head. -/
theorem runHistoryFrom_visited_le_iff (M : TM Id κ Γ Q) (c : Q × Cfg κ Γ xs)
    (n : ℕ) (i : κ) (v : NonemptyInterval ℤ) :
    (M.runHistoryFrom c n).snd.visited i ≤ v ↔
      ∀ m ≤ n, (M.runFrom c m).2.workPos i ∈ v := by
  simp only [History.visited_apply_le_iff, History.configs_snd, List.mem_map,
    Controller.mem_configs_runHistoryFrom, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

end Complexity.TM
