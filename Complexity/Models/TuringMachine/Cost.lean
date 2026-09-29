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
theorem runHistoryFrom_visited_mono (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).visited := by
  intro n k h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  dsimp only
  rw [Controller.runHistoryFrom_add, History.visited_append]
  exact le_sup_left

theorem runHistoryFrom_space_mono [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    Monotone fun n ↦ (M.runHistoryFrom c n).space :=
  fun _ _ h ↦ History.space_mono (M.runHistoryFrom_visited_mono c h)

/-- An interval bounds a tape's visits exactly when it contains every bounded-run head. -/
theorem runHistoryFrom_visited_le_iff (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) (i : κ) (v : NonemptyInterval ℤ) :
    (M.runHistoryFrom c n).visited i ≤ v ↔
      ∀ m ≤ n, (M.runFrom c m).workPos i ∈ v := by
  simp only [History.visited_apply_le_iff, Controller.mem_configs_runHistoryFrom,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- Equal head trajectories give equal visited intervals. -/
theorem runHistoryFrom_visited_congr {κ' Γ' Q' : Type*} [Inhabited Γ'] {ys : Array Γ'}
    (M : TM Id κ Γ Q) (N : TM Id κ' Γ' Q') (c : Cfg κ Γ Q xs)
    (d : Cfg κ' Γ' Q' ys) (n : ℕ) (i : κ) (j : κ')
    (h : ∀ m ≤ n, (M.runFrom c m).workPos i = (N.runFrom d m).workPos j) :
    (M.runHistoryFrom c n).visited i = (N.runHistoryFrom d n).visited j := by
  apply eq_of_forall_ge_iff
  intro v
  simp +contextual only [runHistoryFrom_visited_le_iff, h]

namespace Cfg

/-- Represent external bits by nonblank symbols on input and output. -/
@[simps hasOutput]
instance bitsExecution {κ Q : Type*} (xs : List Bool) :
    Controller.Execution (Cfg κ (Option Bool) Q (xs.map some).toArray)
      Q (Output := List Bool) (input := xs) where
  init q := (rawExecution (xs.map some)).init q
  state_init _ := rfl
  hasOutput cfg ys := cfg.output = (ys.map some).toArray

end Cfg

@[simp] theorem initInput_bits {κ Q : Type*} {F : Type _ → Type*}
    (M : TM F κ (Option Bool) Q) (xs : List Bool) :
    M.initInput (Config := Cfg κ (Option Bool) Q (xs.map some).toArray) xs =
      M.initInput (Config := Cfg κ (Option Bool) Q (xs.map some).toArray) (xs.map some) := rfl

end Complexity.TM
