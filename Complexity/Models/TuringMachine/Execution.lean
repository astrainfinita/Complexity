/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.Execution
public import Complexity.Models.TuringMachine.Deterministic

/-! # Turing machine execution with list and bit-string inputs and outputs -/

@[expose] public section

namespace Complexity.TM

/-- Execute on lists while recording visited work cells for resource accounting. -/
instance execution {κ Γ Q : Type*} [Inhabited Γ] (xs : List Γ) :
    Controller.Execution (TrackedCfg κ Γ Q xs.toArray)
      Q (Output := List Γ) (input := xs) where
  init q := ((rawExecution xs).init q).track
  state_init _ := rfl
  hasOutput cfg ys := cfg.cfg.output = ys.toArray

/-- Represent external bits by nonblank symbols on the input and output tapes. -/
instance bitExecution {κ Q : Type*} (xs : List Bool) :
    Controller.Execution
      (TrackedCfg κ (Option Bool) Q ((xs.map some).toArray))
      Q (Output := List Bool) (input := xs) where
  init q := ((rawExecution (xs.map some)).init q).track
  state_init _ := rfl
  hasOutput cfg ys := cfg.cfg.output = (ys.map some).toArray

/-- The standard list input initializes an ordinary configuration with visit records. -/
@[simp] theorem initInput_tracked {κ Γ Q : Type*} [Inhabited Γ]
    {F : Type _ → Type*} (M : TM F κ Γ Q) (xs : List Γ) :
    M.initInput (Config := TrackedCfg κ Γ Q xs.toArray) xs =
      (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs).track := rfl

/-- Bit inputs occupy nonblank cells before execution starts. -/
@[simp] theorem initInput_bits {κ Q : Type*} {F : Type _ → Type*}
    (M : TM F κ (Option Bool) Q) (xs : List Bool) :
    M.initInput
      (Config := TrackedCfg κ (Option Bool) Q ((xs.map some).toArray)) xs =
      (M.initInput (Config := Cfg κ (Option Bool) Q (xs.map some).toArray)
        (xs.map some)).track := rfl

/-- Unit action time and visited-cell space recover the machine budgets. -/
@[simp] theorem computes_visited_iff {κ Γ Q : Type*} [Inhabited Γ] [Fintype κ]
    (M : TM Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) :
    M.computes (Config := TrackedCfg κ Γ Q xs.toArray) visitedCosts xs ys t s ↔
      M.ComputesInTimeAndSpace xs ys t s := by
  let c := M.initInput (Config := Cfg κ Γ Q xs.toArray) xs
  change (∃ n,
    M.Halted (M.runFrom c.track n) ∧
    (M.runFrom c.track n).cfg.output = ys.toArray ∧
    M.runActionSumFrom (fun _ _ => 1) c.track n ≤ t ∧
    M.spaceUsed c n ≤ s) ↔
    M.Halted (M.runFrom c t) ∧ (M.runFrom c t).output = ys.toArray ∧
      M.spaceUsed c t ≤ s
  simp only [tracked_halted_iff, tracked_runFrom_cfg, Cfg.track_cfg]
  constructor
  · rintro ⟨n, hn, hy, htime, hspace⟩
    let active := M.runActionSumFrom (fun _ _ => 1) c.track n
    have he : M.runFrom c active = M.runFrom c n := by
      simpa only [tracked_runFrom_cfg, Cfg.track_cfg] using
        congrArg TrackedCfg.cfg (M.runFrom_runActionSumFrom_unit c.track n)
    have ha : M.Halted (M.runFrom c active) := he.symm ▸ hn
    have hr := M.runFrom_eq_of_halted c ha htime
    refine ⟨hr.symm ▸ ha, ?_, ?_⟩
    · rwa [hr, he]
    · rw [M.spaceUsed_eq_of_halted c ha htime]
      exact (M.spaceUsed_mono c
        (M.runActionSumFrom_unit_le c.track n)).trans hspace
  · rintro ⟨hn, hy, hs⟩
    exact ⟨t, hn, hy, M.runActionSumFrom_unit_le c.track t, hs⟩

/-- Bit-string execution uses unit time and visited space on nonblank symbols. -/
@[simp] theorem computes_bits_visited_iff {κ Q : Type*} [Fintype κ]
    (M : TM Id κ (Option Bool) Q) (xs ys : List Bool) (t s : ℕ) :
    M.computes (Config := TrackedCfg κ (Option Bool) Q ((xs.map some).toArray))
      visitedCosts xs ys t s ↔
      M.ComputesInTimeAndSpace (xs.map some) (ys.map some) t s := by
  exact computes_visited_iff M (xs.map some) (ys.map some) t s

end Complexity.TM
