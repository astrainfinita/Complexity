/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Cost
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-!
# Deterministic execution and resource bounds

These definitions specialize the choice shape to `Id`. Space counts visited work cells,
including the initial head positions and blank cells, and excludes input and output.
Termination and bounds on all execution prefixes are separate properties.
-/

@[expose] public section

namespace Complexity.TM

/-- Adding a neighbouring position to an integer interval changes only its endpoints. -/
private theorem insert_Icc_of_adjacent {l h p : ℤ} (hlh : l ≤ h)
    (hl : l - 1 ≤ p) (hh : p ≤ h + 1) :
    insert p (Finset.Icc l h) = Finset.Icc (min l p) (max h p) := by
  ext j
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- Execution only appends to the output. -/
theorem output_size_le_runFrom (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (n : ℕ) :
    c.output.size ≤ (M.runFrom c n).output.size := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    have hs : c.output.size ≤ (M.step c).output.size := by
      simp only [step_eq]
      split
      · exact le_rfl
      · simp only [apply_output]
        split <;> simp
    exact hs.trans (ih (M.step c))

/-- The output length is monotone along a bounded run. -/
theorem output_size_runFrom_mono (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    {s t : ℕ} (h : s ≤ t) : (M.runFrom c s).output.size ≤ (M.runFrom c t).output.size := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Controller.runFrom_add]
  exact M.output_size_le_runFrom (M.runFrom c s) u

/-- Work positions visited through time `t`, including time zero. -/
def visited (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (t : ℕ) (i : κ) : Finset ℤ :=
  (Finset.range (t + 1)).image fun s ↦ (M.runFrom c s).workPos i

/-- Include the next position in a finite run's visited cells. -/
theorem visited_succ (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (n : ℕ) (i : κ) :
    M.visited c (n + 1) i = insert ((M.runFrom c (n + 1)).workPos i) (M.visited c n i) := by
  simp only [visited, Finset.range_add_one, Finset.image_insert]

/-- Total distinct work cells visited, counted separately on each tape. -/
def spaceUsed [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (t : ℕ) : ℕ :=
  M.runConfigMaxFrom visitedCosts.space c.track t

theorem visited_mono (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    {s t : ℕ} (h : s ≤ t) (i : κ) : M.visited c s i ⊆ M.visited c t i := by
  apply Finset.image_subset_image
  exact Finset.range_mono (by omega)

theorem spaceUsed_mono [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    {s t : ℕ} (h : s ≤ t) : M.spaceUsed c s ≤ M.spaceUsed c t :=
  M.runConfigMaxFrom_mono visitedCosts.space c.track h

@[simp]
theorem spaceUsed_zero [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    M.spaceUsed c 0 = Fintype.card κ := by
  simp only [spaceUsed, Controller.runConfigMaxFrom_zero]
  exact Cfg.space_track c

/-- Padding a halted run does not visit additional work cells. -/
theorem visited_eq_of_halted (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    {t u : ℕ} (h : M.Halted (M.runFrom c t)) (hu : t ≤ u) (i : κ) :
    M.visited c u i = M.visited c t i := by
  apply Finset.Subset.antisymm ?_ (M.visited_mono c hu i)
  intro j hj
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
  by_cases h₁ : v ≤ t
  · exact Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr (by omega), rfl⟩
  · refine Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), ?_⟩
    rw [M.runFrom_eq_of_halted c h (by omega : t ≤ v)]

theorem spaceUsed_eq_of_halted [Fintype κ] (M : TM Id κ Γ Q)
    (c : Cfg κ Γ Q xs) {t u : ℕ} (h : M.Halted (M.runFrom c t)) (hu : t ≤ u) :
    M.spaceUsed c u = M.spaceUsed c t := by
  apply M.runConfigMaxFrom_eq_of_halted visitedCosts.space
    c.track ?_ hu
  simpa only [tracked_halted_iff, tracked_runFrom_cfg, Cfg.track_cfg] using h

/-- The tracked interval contains exactly the cells visited by the ordinary run. -/
@[simp] theorem tracked_runFrom_visited (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (n : ℕ) (i : κ) :
    let s := (M.runFrom c.track n)
    Finset.Icc (s.visited i).fst (s.visited i).snd = M.visited c n i := by
  dsimp only
  induction n with
  | zero => simp [visited, Controller.runFrom_zero, NonemptyInterval.pure]
  | succ n ih =>
    let s := (M.runFrom c.track n)
    have hp : s.cfg.workPos i - 1 ≤ (M.step s.cfg).workPos i ∧
        (M.step s.cfg).workPos i ≤ s.cfg.workPos i + 1 := by
      rw [TM.step_eq]
      split
      · omega
      · exact Action.workPos_apply_bounds _ _ i
    have hv := s.head_mem i
    rw [Controller.runFrom_succ', tracked_step_visited]
    change Finset.Icc (min (s.visited i).fst ((M.step s.cfg).workPos i))
      (max (s.visited i).snd ((M.step s.cfg).workPos i)) = _
    rw [← insert_Icc_of_adjacent (s.visited i).fst_le_snd (by omega) (by omega), ih]
    simp only [s, tracked_runFrom_cfg, Cfg.track_cfg, ← Controller.runFrom_succ', visited_succ]

/-- A common bound for earlier history and the ordinary run bounds the entire tracked run. -/
theorem tracked_runFrom_within (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs)
    (n : ℕ) {l h : κ → ℤ} (hs : s.Within l h)
    (hv : ∀ i, M.visited s.cfg n i ⊆ Finset.Icc (l i) (h i)) :
    (M.runFrom s n).Within l h := by
  intro i
  have hi := hv i
  rw [← tracked_runFrom_visited] at hi
  have hb := (Finset.Icc_subset_Icc_iff
    ((M.runFrom s.cfg.track n).visited i).fst_le_snd).mp hi
  rw [tracked_runFrom_visited_sup]
  exact ⟨le_min (hs i).1 hb.1, max_le (hs i).2 hb.2⟩

/-- Interval lengths recover the distinct-cell count of the ordinary run. -/
theorem spaceUsed_eq_sum_visited [Fintype κ] (M : TM Id κ Γ Q)
    (c : Cfg κ Γ Q xs) (n : ℕ) :
    M.spaceUsed c n = ∑ i, (M.visited c n i).card := by
  rw [spaceUsed, runConfigMaxFrom_tracked]
  simp only [TrackedCfg.space, ← Int.card_Icc, tracked_runFrom_visited]

/-- The computation eventually reaches a halting state. -/
def Terminates (M : TM Id κ Γ Q) (xs : List Γ) : Prop :=
  ∃ t, M.Halted (M.run (Config := Cfg κ Γ Q xs.toArray) xs t)

/-- The first halting time, excluding the identity steps that pad a halted execution. -/
def HaltsAt (M : TM Id κ Γ Q) (xs : List Γ) (t : ℕ) : Prop :=
  M.Halted (M.run (Config := Cfg κ Γ Q xs.toArray) xs t) ∧
    ∀ u < t, ¬M.Halted (M.run (Config := Cfg κ Γ Q xs.toArray) xs u)

theorem HaltsAt.terminates {M : TM Id κ Γ Q} {xs : List Γ} {t : ℕ}
    (h : M.HaltsAt xs t) : M.Terminates xs := ⟨t, h.1⟩

theorem HaltsAt.unique {M : TM Id κ Γ Q} {xs : List Γ} {s t : ℕ}
    (h : M.HaltsAt xs s) (h' : M.HaltsAt xs t) : s = t := by
  rcases lt_trichotomy s t with h₁ | h₁ | h₁
  · exact (h'.2 s h₁ h.1).elim
  · exact h₁
  · exact (h.2 t h₁ h'.1).elim

/-- Every finite execution prefix uses at most `s` work cells, whether or not the run halts. -/
def UsesSpace [Fintype κ] (M : TM Id κ Γ Q) (xs : List Γ) (s : ℕ) : Prop :=
  ∀ t, M.spaceUsed (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) t ≤ s

/-- By time `t`, the machine has halted with the specified output and has used at most `s` cells. -/
def ComputesInTimeAndSpace [Fintype κ] (M : TM Id κ Γ Q) (xs ys : List Γ)
    (t s : ℕ) : Prop :=
  M.Halted (M.run (Config := Cfg κ Γ Q xs.toArray) xs t) ∧
    (M.run (Config := Cfg κ Γ Q xs.toArray) xs t).output = ys.toArray ∧
    M.spaceUsed (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) t ≤ s

theorem ComputesInTimeAndSpace.terminates [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace xs ys t s) : M.Terminates xs :=
  ⟨t, h.1⟩

/-- A bounded computation controls space at every earlier execution prefix. -/
theorem ComputesInTimeAndSpace.spaceUsed_le [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace xs ys t s) {u : ℕ} (hu : u ≤ t) :
    M.spaceUsed (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) u ≤ s :=
  (M.spaceUsed_mono _ hu).trans h.2.2

/-- A terminating bounded computation controls space along the entire infinite padded run. -/
theorem ComputesInTimeAndSpace.usesSpace [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace xs ys t s) : M.UsesSpace xs s := by
  intro u
  by_cases hu : u ≤ t
  · exact h.spaceUsed_le hu
  · rw [M.spaceUsed_eq_of_halted
      (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs) h.1
      (by omega : t ≤ u)]
    exact h.2.2

end Complexity.TM
