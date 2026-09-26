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

namespace TrackedCfg

@[simps]
instance : Controller.HasState (TrackedCfg κ Γ Q xs) Q where
  state s := Controller.state s.cfg

@[simps]
instance : Controller.Observe (TrackedCfg κ Γ Q xs) (Γ × (κ → Γ)) where
  observe s := observe s.cfg

/-- Apply an action and extend the recorded intervals to include the new heads. -/
@[simps]
instance : Controller.Apply (TrackedCfg κ Γ Q xs) (Action κ Γ Q) where
  apply a s :=
    let c := apply a s.cfg
    ⟨c, fun i ↦ s.visited i ⊔ NonemptyInterval.pure (c.workPos i),
      fun _ ↦ ⟨min_le_right _ _, le_max_right _ _⟩⟩

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

instance [Fintype κ] (s : TrackedCfg κ Γ Q xs) (l h : κ → ℤ) :
    Decidable (s.Within l h) := by
  unfold Within
  infer_instance

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
@[simps time, simps -fullyApplied space]
def visitedCosts [Fintype κ] : CostModel (Action κ Γ Q) (TrackedCfg κ Γ Q xs) where
  time := (fun _ _ => 1)
  space := TrackedCfg.space

/-- Forgetting visit records after one step recovers the ordinary machine step. -/
@[simp] theorem tracked_step_cfg (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) :
    (M.step s).cfg =
      M.step s.cfg := by
  by_cases h : M.halt s.cfg.state = true <;>
    simp [Controller.step, Controller.stepWith, h]

/-- Each step extends the interval to its new head; halted padding stays within it. -/
theorem tracked_step_visited (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) (i : κ) :
    (M.step s).visited i =
      s.visited i ⊔ NonemptyInterval.pure ((M.step s.cfg).workPos i) := by
  by_cases h : M.halt s.cfg.state = true
  · simp only [Controller.step_of_halted M s h,
      M.step_of_halted s.cfg h]
    exact (sup_eq_left.mpr (s.head_mem i)).symm
  · simp [Controller.step, Controller.stepWith, h]

/-- A step visits only its new head position in addition to its prior interval. -/
theorem mem_tracked_step_visited (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    (i : κ) (p : ℤ) :
    p ∈ (M.step s).visited i ↔ p ∈ s.visited i ∨ p = (M.step s.cfg).workPos i := by
  have hp := M.step_workPos_bounds s.cfg i
  have hv := s.head_mem i
  rw [tracked_step_visited]
  simp only [NonemptyInterval.mem_def, NonemptyInterval.fst_sup, NonemptyInterval.snd_sup,
    NonemptyInterval.pure_fst, NonemptyInterval.pure_snd]
  omega

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

/-- Sequential runs join prior visits with the next block's fresh interval. -/
theorem tracked_runFrom_visited_add (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    (m n : ℕ) (i : κ) :
    (M.runFrom s (m + n)).visited i = (M.runFrom s m).visited i ⊔
      (M.runFrom (M.runFrom s.cfg m).track n).visited i := by
  rw [Controller.runFrom_add, tracked_runFrom_visited_sup, tracked_runFrom_cfg]

/-- A freshly tracked interval contains exactly the positions reached within the run. -/
theorem mem_tracked_runFrom_visited (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) (i : κ) (p : ℤ) :
    p ∈ (M.runFrom c.track n).visited i ↔ ∃ m ≤ n, p = (M.runFrom c m).workPos i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Controller.runFrom_succ', mem_tracked_step_visited, ih]
    simp only [tracked_runFrom_cfg, Cfg.track_cfg, ← Controller.runFrom_succ',
      Nat.le_add_one_iff, or_and_right, exists_or, exists_eq_left]

/-- A freshly tracked run lies in an interval exactly when all its heads do. -/
theorem tracked_runFrom_visited_le_iff (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) (i : κ) (v : NonemptyInterval ℤ) :
    (M.runFrom c.track n).visited i ≤ v ↔
      ∀ m ≤ n, (M.runFrom c m).workPos i ∈ v := by
  rw [← NonemptyInterval.coe_subset_coe]
  simp only [Set.subset_def, SetLike.mem_coe, mem_tracked_runFrom_visited]
  exact ⟨fun h m hm ↦ h _ ⟨m, hm, rfl⟩, fun h _ ⟨m, hm, hp⟩ ↦ hp ▸ h m hm⟩

/-- Equal work-head trajectories give equal freshly tracked intervals. -/
theorem tracked_runFrom_visited_congr {κ' Γ' Q' : Type*} [Inhabited Γ'] {ys : Array Γ'}
    (M : TM Id κ Γ Q) (N : TM Id κ' Γ' Q') (c : Cfg κ Γ Q xs)
    (d : Cfg κ' Γ' Q' ys) (n : ℕ) (i : κ) (j : κ')
    (h : ∀ m ≤ n, (M.runFrom c m).workPos i = (N.runFrom d m).workPos j) :
    (M.runFrom c.track n).visited i = (N.runFrom d.track n).visited j := by
  apply SetLike.ext
  intro p
  simp only [mem_tracked_runFrom_visited]
  exact exists_congr fun m ↦ and_congr_right fun hm ↦ by rw [h m hm]

/-- A common bound for earlier history and fresh visits bounds the entire tracked run. -/
theorem tracked_runFrom_within (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    (n : ℕ) {l h : κ → ℤ} (hs : s.Within l h)
    (hv : (M.runFrom s.cfg.track n).Within l h) :
    (M.runFrom s n).Within l h := by
  intro i
  rw [tracked_runFrom_visited_sup]
  exact ⟨le_min (hs i).1 (hv i).1, max_le (hs i).2 (hv i).2⟩

/-- A bound at the endpoint covers each earlier tracked prefix. -/
theorem tracked_runFrom_within_mono (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    {m n : ℕ} {l h : κ → ℤ} (hm : m ≤ n) (hn : (M.runFrom s n).Within l h) :
    (M.runFrom s m).Within l h := by
  intro i
  have hv := M.tracked_runFrom_visited_mono s hm i
  exact ⟨(hn i).1.trans hv.1, hv.2.trans (hn i).2⟩

/-- Growing intervals make peak space equal the final space, also when resuming a run. -/
@[simp] theorem runConfigMaxFrom_tracked [Fintype κ] (M : TM Id κ Γ Q)
    (s : TrackedCfg κ Γ Q xs) (n : ℕ) :
    M.runConfigMaxFrom TrackedCfg.space s n =
      (M.runFrom s n).space := by
  apply Nat.le_antisymm ?_
    (M.space_le_runConfigMaxFrom TrackedCfg.space s (Nat.le_refl n))
  apply (M.runConfigMaxFrom_le_iff TrackedCfg.space s n _).2
  intro m hm
  exact TrackedCfg.space_mono fun i ↦ M.tracked_runFrom_visited_mono s hm i

namespace TrackedCfg

/-- Execute on lists while recording visited work cells for resource accounting. -/
@[simps hasOutput]
instance {κ Γ Q : Type*} [Inhabited Γ] (xs : List Γ) :
    Controller.Execution (TrackedCfg κ Γ Q xs.toArray)
      Q (Output := List Γ) (input := xs) where
  init q := ((rawExecution xs).init q).track
  state_init _ := rfl
  hasOutput cfg ys := cfg.cfg.output = ys.toArray

/-- Represent external bits by nonblank symbols on the input and output tapes. -/
@[simps hasOutput]
instance bitsExecution {κ Q : Type*} (xs : List Bool) :
    Controller.Execution
      (TrackedCfg κ (Option Bool) Q ((xs.map some).toArray))
      Q (Output := List Bool) (input := xs) where
  init q := ((rawExecution (xs.map some)).init q).track
  state_init _ := rfl
  hasOutput cfg ys := cfg.cfg.output = (ys.map some).toArray

end TrackedCfg

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

@[simp] theorem tracked_run_cfg (M : TM Id κ Γ Q) (xs : List Γ) (n : ℕ) :
    (M.run (TrackedCfg κ Γ Q xs.toArray) xs n).cfg = M.run (Cfg κ Γ Q xs.toArray) xs n :=
  M.tracked_runFrom_cfg _ n

@[simp↓] theorem runConfigMax_tracked [Fintype κ] (M : TM Id κ Γ Q)
    (xs : List Γ) (n : ℕ) :
    M.runConfigMax (Config := TrackedCfg κ Γ Q xs.toArray) TrackedCfg.space xs n =
      (M.run (TrackedCfg κ Γ Q xs.toArray) xs n).space :=
  M.runConfigMaxFrom_tracked _ n

end Complexity.TM
