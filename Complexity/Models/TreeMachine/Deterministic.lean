/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Cost

/-!
# Deterministic tree machines and resource bounds

`timeUsed` counts active transitions and `cost` charges the size written to the selected register.
The generic controller space measure records the largest total expanded tree size seen so far.
All three ignore halted padding.
The cumulative cost bounds time and, together with initial mass, every intermediate mass.
A running `nop` costs one and preserves the register bank.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {k : ℕ} {Q : Type*}

theorem mass_input_le [NeZero k] (M : TreeMachine Id k Q) (a : Tree) :
    (M.initInput (Config := Cfg k Q) a).mass ≤ a.size + k := by
  change (∑ j, (input 0 a j).size) ≤ _
  rw [sum_size_input]
  omega

/-- Cumulative destination-size cost, excluding halted padding. -/
def cost (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) : ℕ :=
  M.runActionSumFrom treeCosts.time c t

@[simp] theorem cost_zero (M : TreeMachine Id k Q) (c : Cfg k Q) : M.cost c 0 = 0 := rfl

theorem cost_succ (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.cost c (t + 1) = M.stepCost treeCosts.time c + M.cost (M.step c) t := rfl

theorem cost_succ' (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.cost c (t + 1) = M.cost c t + M.stepCost treeCosts.time (M.runFrom c t) :=
  Transition.runCost_succ' M.step (fun c _ => M.stepCost treeCosts.time c) t c

theorem cost_add (M : TreeMachine Id k Q) (c : Cfg k Q) (s t : ℕ) :
    M.cost c (s + t) = M.cost c s + M.cost (M.runFrom c s) t :=
  Controller.runActionSumFrom_add M treeCosts.time c s t

theorem cost_mono (M : TreeMachine Id k Q) (c : Cfg k Q) {s t : ℕ} (h : s ≤ t) :
    M.cost c s ≤ M.cost c t :=
  Controller.runActionSumFrom_mono M treeCosts.time c h

@[simp] theorem cost_of_halted (M : TreeMachine Id k Q) (c : Cfg k Q)
    (h : M.Halted c) (t : ℕ) : M.cost c t = 0 :=
  Controller.runActionSumFrom_of_halted M treeCosts.time c h t

theorem cost_eq_of_halted (M : TreeMachine Id k Q) (c : Cfg k Q)
    {t u : ℕ} (h : M.Halted (M.runFrom c t)) (hu : t ≤ u) : M.cost c u = M.cost c t :=
  Controller.runActionSumFrom_eq_of_halted M treeCosts.time c h hu

/-- Number of active transitions, independent of the sizes of their operands. -/
def timeUsed (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) : ℕ :=
  M.runActionSumFrom (fun _ _ => 1) c t

theorem timeUsed_le_cost (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.timeUsed c t ≤ M.cost c t := by
  unfold timeUsed cost Controller.runActionSumFrom
  apply Transition.runCost_le_runCost
  intro d
  simp only [Controller.stepCost, treeCosts_time]
  split
  · exact le_rfl
  · exact Op.timeCost_pos _ _

theorem mass_step_le (M : TreeMachine Id k Q) (c : Cfg k Q) :
    (M.step c).mass ≤ c.mass + M.stepCost treeCosts.time c := by
  by_cases h : M.Halted c
  · rw [M.stepCost_of_halted _ c h, Nat.add_zero, M.step_of_halted c h]
  · change (M.step c).mass ≤ c.mass +
      (if M.halt c.state then 0 else treeCosts.time ((M.transition c.state (observe c)).run) c)
    simpa [step_eq, show M.halt c.state ≠ true from h] using
      c.mass_apply_le ((M.transition c.state (observe c)).run)

theorem mass_runFrom_le (M : TreeMachine Id k Q) (c : Cfg k Q) {s t : ℕ} (h : s ≤ t) :
    (M.runFrom c s).mass ≤ c.mass + M.cost c t :=
  Transition.potential_runN_le_of_le _ _ _ M.mass_step_le h c

theorem runConfigMaxFrom_le_mass_add_cost (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.runConfigMaxFrom treeCosts.space c t ≤ c.mass + M.cost c t := by
  apply (Controller.runConfigMaxFrom_le_iff M treeCosts.space c t _).2
  intro s hs
  exact M.mass_runFrom_le c hs

theorem timeUsed_eq_of_not_halted (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ)
    (h : ∀ s < t, ¬M.Halted (M.runFrom c s)) : M.timeUsed c t = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h₁ := ih (fun s hs ↦ h s (by omega))
    have h₂ := h t (by omega)
    unfold timeUsed Controller.runActionSumFrom at *
    rw [Transition.runCost_succ', h₁]
    change t + (if M.halt (M.runFrom c t).state then 0 else 1) = t + 1
    simp [show M.halt (M.runFrom c t).state ≠ true from h₂]

section Canonical

variable [NeZero k]

/-- The computation eventually reaches a halting state. -/
def Terminates (M : TreeMachine Id k Q) (a : Tree) : Prop :=
  ∃ t, M.Halted (M.run (Config := Cfg k Q) a t)

/-- The first halting time, with the same convention as for a multi-tape machine. -/
def HaltsAt (M : TreeMachine Id k Q) (a : Tree) (t : ℕ) : Prop :=
  M.Halted (M.run (Config := Cfg k Q) a t) ∧ ∀ u < t, ¬M.Halted (M.run (Config := Cfg k Q) a u)

theorem HaltsAt.terminates {M : TreeMachine Id k Q} {a : Tree} {t : ℕ}
    (h : M.HaltsAt a t) : M.Terminates a := ⟨t, h.1⟩

theorem HaltsAt.unique {M : TreeMachine Id k Q} {a : Tree} {s t : ℕ}
    (h : M.HaltsAt a s) (h' : M.HaltsAt a t) : s = t := by
  rcases lt_trichotomy s t with h₁ | h₁ | h₁
  · exact (h'.2 s h₁ h.1).elim
  · exact h₁
  · exact (h.2 t h₁ h'.1).elim

/-- Any halting endpoint contains a first halting time. -/
theorem exists_haltsAt_le (M : TreeMachine Id k Q) (a : Tree) {t : ℕ}
    (h : M.Halted (M.run (Config := Cfg k Q) a t)) : ∃ n ≤ t, M.HaltsAt a n := by
  classical
  have h' : M.Terminates a := ⟨t, h⟩
  exact ⟨Nat.find h', Nat.find_min' h' h, Nat.find_spec h',
    fun _ hn ↦ Nat.find_min h' hn⟩

theorem Terminates.exists_haltsAt {M : TreeMachine Id k Q} {a : Tree}
    (h : M.Terminates a) : ∃ t, M.HaltsAt a t := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨n, _, hn⟩ := M.exists_haltsAt_le a ht
  exact ⟨n, hn⟩

theorem HaltsAt.le_cost {M : TreeMachine Id k Q} {a : Tree} {t : ℕ}
    (h : M.HaltsAt a t) :
    t ≤ M.cost (M.initInput (Config := Cfg k Q) a) t := by
  have h₁ := M.timeUsed_le_cost
    (M.initInput (Config := Cfg k Q) a) t
  rwa [M.timeUsed_eq_of_not_halted
    (M.initInput (Config := Cfg k Q) a) t h.2] at h₁

/-- Every finite prefix stays within the given expanded-tree space bound. -/
def UsesSpace (M : TreeMachine Id k Q) (a : Tree) (s : ℕ) : Prop :=
  ∀ t, M.runConfigMax (Config := Cfg k Q) treeCosts.space a t ≤ s

/-- Compute a tree in register zero within a cumulative destination-size time budget
and a maximum expanded-tree space budget. The transition count is an existential witness,
since the external time charge depends on the size written to the selected register. -/
def ComputesInTimeAndSpace (M : TreeMachine Id k Q) (a : Tree)
    (b : Tree) (t s : ℕ) : Prop :=
  Controller.computes (Config := Cfg k Q) M treeCosts a b t s

/-- A halted run's time budget also bounds its peak space by input size and register count. -/
theorem ComputesInTimeAndSpace.of_run {M : TreeMachine Id k Q} {a b : Tree} {n t s : ℕ}
    (hh : M.Halted (M.run (Config := Cfg k Q) a n))
    (ho : (M.run (Config := Cfg k Q) a n).regs 0 = b)
    (ht : M.runActionSum treeCosts.time a n ≤ t) (hs : a.size + k + t ≤ s) :
    M.ComputesInTimeAndSpace a b t s := by
  refine ⟨n, hh, ho, ht, ?_⟩
  exact (M.runConfigMaxFrom_le_mass_add_cost _ n).trans
    ((Nat.add_le_add (mass_input_le M a) ht).trans hs)

/-- Replace a computation's space budget with the bound supplied by its time cost. -/
theorem ComputesInTimeAndSpace.space_of_time {M : TreeMachine Id k Q} {a b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) :
    M.ComputesInTimeAndSpace a b t (a.size + k + t) := by
  obtain ⟨n, hh, ho, ht, _⟩ := h
  exact .of_run hh ho ht le_rfl

theorem ComputesInTimeAndSpace.terminates {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s) :
    M.Terminates a := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩

/-- The witness can be chosen to be the first halting time, which is at most the time budget. -/
theorem ComputesInTimeAndSpace.exists_haltsAt {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s) :
    ∃ n ≤ t, M.HaltsAt a n ∧ (M.run (Config := Cfg k Q) a n).regs 0 = b ∧
      M.cost (M.initInput (Config := Cfg k Q) a) n ≤ t ∧
      M.runConfigMax (Config := Cfg k Q) treeCosts.space a n ≤ s := by
  obtain ⟨u, hu, ha, ht, hs⟩ := h
  change (M.run (Config := Cfg k Q) a u).regs 0 = b at ha
  obtain ⟨n, hn, hh⟩ := M.exists_haltsAt_le a hu
  have hc := (M.runActionSum_mono treeCosts.time a hn).trans ht
  refine ⟨n, hh.le_cost.trans hc, hh, ?_, hc,
    (M.runConfigMax_mono treeCosts.space a hn).trans hs⟩
  rwa [M.run_eq_of_halted a hh.1 hn] at ha

/-- A terminating bounded computation controls space along the entire padded execution. -/
theorem ComputesInTimeAndSpace.usesSpace {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s) :
    M.UsesSpace a s :=
  fun u => Controller.computes_runConfigMax_le h u

theorem ComputesInTimeAndSpace.cost_le {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s)
    (u : ℕ) : M.cost (M.initInput (Config := Cfg k Q) a) u ≤ t :=
  Controller.computes_runActionSum_le h u

/-- The time budget controls space even without using the explicit space budget. -/
theorem ComputesInTimeAndSpace.runConfigMaxFrom_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) (u : ℕ) :
    M.runConfigMaxFrom treeCosts.space
      (M.initInput (Config := Cfg k Q) a) u ≤
      (M.initInput (Config := Cfg k Q) a).mass + t :=
  (M.runConfigMaxFrom_le_mass_add_cost _ u).trans (Nat.add_le_add_left (h.cost_le u) _)

theorem ComputesInTimeAndSpace.mass_le {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s)
    (u : ℕ) : (M.run (Config := Cfg k Q) a u).mass ≤ s :=
  (M.space_le_runConfigMax treeCosts.space a (Nat.le_refl u)).trans
    (h.usesSpace u)

theorem ComputesInTimeAndSpace.mass_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) (u : ℕ) :
    (M.run (Config := Cfg k Q) a u).mass ≤ (M.initInput (Config := Cfg k Q) a).mass + t :=
  (M.space_le_runConfigMax treeCosts.space a (Nat.le_refl u)).trans
    (h.runConfigMaxFrom_le_mass_add_time u)

/-- The output register is bounded by the explicit space budget. -/
theorem ComputesInTimeAndSpace.output_size_le_space
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) : b.size ≤ s := by
  have hm := h.mass_le
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run (Config := Cfg k Q) a n).reg_size_le_mass 0).trans (hm n)

/-- The output size is bounded by initial mass and the time budget. -/
theorem ComputesInTimeAndSpace.output_size_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) :
    b.size ≤ (M.initInput (Config := Cfg k Q) a).mass + t := by
  have hm := h.mass_le_mass_add_time
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run (Config := Cfg k Q) a n).reg_size_le_mass 0).trans (hm n)

theorem ComputesInTimeAndSpace.mono {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s t' s' : ℕ} (h : M.ComputesInTimeAndSpace a b t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesInTimeAndSpace a b t' s' :=
  Controller.computes_mono h ht hs

end Canonical

end Complexity.TreeMachine
