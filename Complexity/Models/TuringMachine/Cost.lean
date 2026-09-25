/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Basic
public import Complexity.Control.Cost
public import Complexity.Control.Controller.Cost
public import Complexity.Control.Transition.Simulation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Basic
public import Mathlib.Order.Interval.Basic

/-!
# Local costs for Turing machines with visited-cell accounting

`TrackedCfg` records a nonempty interval on each work tape, containing its current
head. A head moves by at most one cell per action, so these intervals record exactly
the visited cells. The machine observes only the underlying configuration. Unit
action costs and interval lengths recover transition time and visited-cell space.
Initial head positions and the final configuration are included; halting padding
performs no action.
-/

@[expose] public section

namespace Complexity.TM

/-- A configuration with external records of the work cells visited so far. -/
@[ext] structure TrackedCfg (κ : Type*) (Γ Q : Type*) [Inhabited Γ] (xs : Array Γ) where
  /-- The machine's ordinary data and control state. -/
  cfg : Cfg κ Γ Q xs
  /-- The nonempty interval of visited positions on each work tape. -/
  visited : κ → NonemptyInterval ℤ
  /-- Every recorded interval contains its current work head. -/
  head_mem : ∀ i, (visited i).fst ≤ cfg.workPos i ∧ cfg.workPos i ≤ (visited i).snd

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Start recording visits from the current heads of an existing configuration. -/
@[simps cfg visited]
def Cfg.track (c : Cfg κ Γ Q xs) : TrackedCfg κ Γ Q xs :=
  ⟨c, fun i ↦ NonemptyInterval.pure (c.workPos i), fun _ ↦ ⟨le_rfl, le_rfl⟩⟩

@[simps]
instance TrackedCfg.instHasState : Controller.HasState (TrackedCfg κ Γ Q xs) Q where
  state s := Controller.state s.cfg

@[simps]
instance TrackedCfg.instObserve : Controller.Observe (TrackedCfg κ Γ Q xs) (Γ × (κ → Γ)) where
  observe s := observe s.cfg

/-- Apply an action and extend the recorded intervals to include the new heads. -/
@[simps]
instance : Controller.Apply (TrackedCfg κ Γ Q xs) (Action κ Γ Q) where
  apply a s :=
    let c := apply a s.cfg
    ⟨c, fun i ↦ s.visited i ⊔ NonemptyInterval.pure (c.workPos i),
      fun _ ↦ ⟨min_le_right _ _, le_max_right _ _⟩⟩

namespace TrackedCfg

/-- Relabel the control state while preserving tape data and the complete visit history. -/
@[simps -fullyApplied cfg visited]
def mapState {Q' : Type*} (f : Q → Q') (s : TrackedCfg κ Γ Q xs) :
    TrackedCfg κ Γ Q' xs :=
  ⟨s.cfg.mapState f, s.visited, s.head_mem⟩

@[simp] theorem mapState_track {Q' : Type*} (f : Q → Q') (c : Cfg κ Γ Q xs) :
    c.track.mapState f = (c.mapState f).track := rfl

/-- Total visited-cell space, computed from interval lengths without enumerating cells. -/
def space [Fintype κ] (s : TrackedCfg κ Γ Q xs) : ℕ :=
  ∑ i, ((s.visited i).snd + 1 - (s.visited i).fst).toNat

@[simp] theorem space_mapState [Fintype κ] {Q' : Type*} (f : Q → Q')
    (s : TrackedCfg κ Γ Q xs) : (s.mapState f).space = s.space := rfl

/-- Enlarging every recorded interval cannot reduce space. -/
theorem space_mono [Fintype κ] {s t : TrackedCfg κ Γ Q xs}
    (h : ∀ i, s.visited i ≤ t.visited i) : s.space ≤ t.space := by
  apply Finset.sum_le_sum
  intro i _
  have hl := (h i).1
  have hr := (h i).2
  omega

/-- Every recorded interval stays inside the specified bounds. -/
def Within (s : TrackedCfg κ Γ Q xs) (l h : κ → ℤ) : Prop :=
  ∀ i, l i ≤ (s.visited i).fst ∧ (s.visited i).snd ≤ h i

theorem Within.head {s : TrackedCfg κ Γ Q xs} {l h : κ → ℤ}
    (hs : s.Within l h) (i : κ) :
    l i ≤ s.cfg.workPos i ∧ s.cfg.workPos i ≤ h i :=
  ⟨(hs i).1.trans (s.head_mem i).1, (s.head_mem i).2.trans (hs i).2⟩

@[simp] theorem within_mapState {Q' : Type*} (f : Q → Q') (s : TrackedCfg κ Γ Q xs)
    (l h : κ → ℤ) : (s.mapState f).Within l h ↔ s.Within l h := Iff.rfl

/-- An action preserves a common bound exactly when its new heads remain inside it. -/
theorem within_apply_iff (a : Action κ Γ Q) (s : TrackedCfg κ Γ Q xs) (l h : κ → ℤ) :
    (apply a s).Within l h ↔ s.Within l h ∧
      ∀ i, l i ≤ (apply a s.cfg).workPos i ∧
        (apply a s.cfg).workPos i ≤ h i := by
  simp only [Within, apply_visited, NonemptyInterval.fst_sup, NonemptyInterval.snd_sup,
    NonemptyInterval.pure, le_min_iff, max_le_iff, forall_and]
  tauto

theorem space_le_of_within [Fintype κ] (s : TrackedCfg κ Γ Q xs) (l h : κ → ℤ)
    (hs : s.Within l h) : s.space ≤ ∑ i, (h i + 1 - l i).toNat := by
  apply Finset.sum_le_sum
  intro i _
  have := hs i
  omega

end TrackedCfg

@[simp] theorem Cfg.space_track [Fintype κ] (c : Cfg κ Γ Q xs) :
    c.track.space = Fintype.card κ := by
  simp [TrackedCfg.space, NonemptyInterval.pure]

/-- Recording visited cells does not affect the halting condition. -/
@[simp] theorem tracked_halted_iff (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) :
    M.Halted s ↔ M.Halted s.cfg := Iff.rfl

/-- Unit transition time and the total historical work-cell footprint. -/
@[simps]
def visitedCosts [Fintype κ] : CostModel (Action κ Γ Q) (TrackedCfg κ Γ Q xs) where
  time := (fun _ _ => 1)
  space := TrackedCfg.space

/-- Forgetting visit records after one step recovers the ordinary machine step. -/
@[simp] theorem tracked_step_cfg (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) :
    (M.step s).cfg =
      M.step s.cfg := by
  by_cases h : M.halt s.cfg.state = true <;>
    simp [Controller.step, Controller.stepWith, Choice.Interpretation.id, h]

/-- Each step extends the interval to its new head; halted padding stays within it. -/
theorem tracked_step_visited (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) (i : κ) :
    (M.step s).visited i =
      s.visited i ⊔ NonemptyInterval.pure ((M.step s.cfg).workPos i) := by
  by_cases h : M.halt s.cfg.state = true
  · simp only [Controller.step_of_halted M s h,
      M.step_of_halted s.cfg h]
    exact (sup_eq_left.mpr (s.head_mem i)).symm
  · simp [Controller.step, Controller.stepWith, Choice.Interpretation.id, h]

/-- Recording visits preserves every ordinary execution prefix. -/
@[simp] theorem tracked_runFrom_cfg (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) (n : ℕ) :
    (M.runFrom s n).cfg =
      M.runFrom s.cfg n :=
  (Transition.runN_map TrackedCfg.cfg (fun s ↦ (M.tracked_step_cfg s).symm) s n).symm

/-- Prior history joins with the interval recorded by the same run from a singleton history.
This compares executions without resetting the history of the running configuration. -/
theorem tracked_runFrom_visited_sup (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    (n : ℕ) (i : κ) :
    (M.runFrom s n).visited i =
      s.visited i ⊔ (M.runFrom s.cfg.track n).visited i := by
  induction n with
  | zero => exact (sup_eq_left.mpr (s.head_mem i)).symm
  | succ n ih =>
    simp only [Controller.runFrom_succ', tracked_step_visited,
      tracked_runFrom_cfg, Cfg.track_cfg, ih, sup_assoc]

/-- Recorded intervals only grow along an execution, including any prior history. -/
theorem tracked_runFrom_visited_mono (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    {m n : ℕ} (h : m ≤ n) (i : κ) :
    (M.runFrom s m).visited i ≤
      (M.runFrom s n).visited i := by
  apply (monotone_nat_of_le_succ (f := fun n ↦
    (M.runFrom s n).visited i) ?_) h
  intro n
  rw [Controller.runFrom_succ', tracked_step_visited]
  exact le_sup_left

/-- Growing intervals make peak space equal the final space, also when resuming a run. -/
@[simp] theorem runConfigMaxFrom_tracked [Fintype κ] (M : TM Id κ Γ Q)
    (s : TrackedCfg κ Γ Q xs) (n : ℕ) :
    M.runConfigMaxFrom visitedCosts.space s n =
      (M.runFrom s n).space := by
  apply Nat.le_antisymm ?_
    (M.space_le_runConfigMaxFrom visitedCosts.space s (Nat.le_refl n))
  apply (M.runConfigMaxFrom_le_iff visitedCosts.space s n _).2
  intro m hm
  exact TrackedCfg.space_mono fun i ↦ M.tracked_runFrom_visited_mono s hm i

end Complexity.TM
