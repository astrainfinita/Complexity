/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Cost

/-!
# Deterministic tree machines and resource bounds

History length counts active transitions; `cost` charges the size written to the selected register.
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
  M.runActionSumFrom Action.timeCost c t

@[simp] theorem cost_zero (M : TreeMachine Id k Q) (c : Cfg k Q) : M.cost c 0 = 0 := rfl

theorem cost_succ (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.cost c (t + 1) = M.stepCost Action.timeCost c + M.cost (M.step c) t :=
  M.runActionSumFrom_succ Action.timeCost c t

theorem cost_succ' (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.cost c (t + 1) = M.cost c t + M.stepCost Action.timeCost (M.runFrom c t) :=
  M.runActionSumFrom_succ' Action.timeCost c t

theorem cost_add (M : TreeMachine Id k Q) (c : Cfg k Q) (s t : ℕ) :
    M.cost c (s + t) = M.cost c s + M.cost (M.runFrom c s) t :=
  Controller.runActionSumFrom_add M Action.timeCost c s t

theorem cost_mono (M : TreeMachine Id k Q) (c : Cfg k Q) {s t : ℕ} (h : s ≤ t) :
    M.cost c s ≤ M.cost c t :=
  Controller.runActionSumFrom_mono M Action.timeCost c h

@[simp] theorem cost_of_halted (M : TreeMachine Id k Q) (c : Cfg k Q)
    (h : M.Halted c) (t : ℕ) : M.cost c t = 0 :=
  Controller.runActionSumFrom_of_halted M Action.timeCost c h t

theorem cost_eq_of_halted (M : TreeMachine Id k Q) (c : Cfg k Q)
    {t u : ℕ} (h : M.Halted (M.runFrom c t)) (hu : t ≤ u) : M.cost c u = M.cost c t :=
  Controller.runActionSumFrom_eq_of_halted M Action.timeCost c h hu

theorem length_runHistoryFrom_le_cost (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    (M.runHistoryFrom c t).length ≤ M.cost c t := by
  rw [← M.runActionSumFrom_unit]
  exact M.runActionSumFrom_mono_cost
    (fun a c ↦ Nat.succ_le_of_lt (Op.timeCost_pos a.op c.regs)) c t

theorem runConfigMaxFrom_le_mass_add_cost (M : TreeMachine Id k Q) (c : Cfg k Q) (t : ℕ) :
    M.runConfigMaxFrom Cfg.mass c t ≤ c.mass + M.cost c t := by
  simpa [Controller.runConfigMaxFrom, cost, Controller.runActionSumFrom] using
    (M.runHistoryFrom c t).configSup_le_add_actionSum Cfg.mass Action.timeCost
      (fun a c _ ↦ c.mass_apply_le a)

theorem mass_runFrom_le (M : TreeMachine Id k Q) (c : Cfg k Q) {s t : ℕ} (h : s ≤ t) :
    (M.runFrom c s).mass ≤ c.mass + M.cost c t :=
  (M.space_le_runConfigMaxFrom Cfg.mass c h).trans (M.runConfigMaxFrom_le_mass_add_cost c t)

section Canonical

variable [NeZero k]

/-- The computation eventually reaches a halting state. -/
def Terminates (M : TreeMachine Id k Q) (a : Tree) : Prop :=
  ∃ t, M.Halted (M.run (Cfg k Q) a t)

/-- The first halting time, with the same convention as for a multi-tape machine. -/
def HaltsAt (M : TreeMachine Id k Q) (a : Tree) (t : ℕ) : Prop :=
  M.Halted (M.run (Cfg k Q) a t) ∧ ∀ u < t, ¬M.Halted (M.run (Cfg k Q) a u)

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
    (h : M.Halted (M.run (Cfg k Q) a t)) : ∃ n ≤ t, M.HaltsAt a n := by
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
  have hc := M.length_runHistoryFrom_le_cost (M.initInput (Config := Cfg k Q) a) t
  rwa [M.length_runHistoryFrom_eq _ _ h.2] at hc

/-- Every finite prefix stays within the given expanded-tree space bound. -/
def UsesSpace (M : TreeMachine Id k Q) (a : Tree) (s : ℕ) : Prop :=
  ∀ t, M.runConfigMax (Config := Cfg k Q) Cfg.mass a t ≤ s

/-- Compute a tree in register zero within a cumulative destination-size time budget
and a maximum expanded-tree space budget. The transition count is an existential witness,
since the external time charge depends on the size written to the selected register. -/
def ComputesInTimeAndSpace (M : TreeMachine Id k Q) (a : Tree)
    (b : Tree) (t s : ℕ) : Prop :=
  M.computes (Config := Cfg k Q)
    (fun h ↦ h.actionSum Action.timeCost) (fun h ↦ h.configSup Cfg.mass) a b t s

/-- A halted run's time budget also bounds its peak space by input size and register count. -/
theorem ComputesInTimeAndSpace.of_run {M : TreeMachine Id k Q} {a b : Tree} {n t s : ℕ}
    (hh : M.Halted (M.run (Cfg k Q) a n))
    (ho : (M.run (Cfg k Q) a n).regs 0 = b)
    (ht : M.runActionSum Action.timeCost a n ≤ t) (hs : a.size + k + t ≤ s) :
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
    ∃ n ≤ t, M.HaltsAt a n ∧ (M.run (Cfg k Q) a n).regs 0 = b ∧
      M.cost (M.initInput (Config := Cfg k Q) a) n ≤ t ∧
      M.runConfigMax (Config := Cfg k Q) Cfg.mass a n ≤ s := by
  obtain ⟨u, hu, ha, ht, hs⟩ := h
  change (M.run (Cfg k Q) a u).regs 0 = b at ha
  obtain ⟨n, hn, hh⟩ := M.exists_haltsAt_le a hu
  have hc := (M.runActionSum_mono Action.timeCost a hn).trans ht
  refine ⟨n, hh.le_cost.trans hc, hh, ?_, hc,
    (M.runConfigMax_mono Cfg.mass a hn).trans hs⟩
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
    M.runConfigMaxFrom Cfg.mass
      (M.initInput (Config := Cfg k Q) a) u ≤
      (M.initInput (Config := Cfg k Q) a).mass + t :=
  (M.runConfigMaxFrom_le_mass_add_cost _ u).trans (Nat.add_le_add_left (h.cost_le u) _)

theorem ComputesInTimeAndSpace.mass_le {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace a b t s)
    (u : ℕ) : (M.run (Cfg k Q) a u).mass ≤ s :=
  (M.space_le_runConfigMax Cfg.mass a (Nat.le_refl u)).trans
    (h.usesSpace u)

theorem ComputesInTimeAndSpace.mass_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) (u : ℕ) :
    (M.run (Cfg k Q) a u).mass ≤ (M.initInput (Config := Cfg k Q) a).mass + t :=
  (M.space_le_runConfigMax Cfg.mass a (Nat.le_refl u)).trans
    (h.runConfigMaxFrom_le_mass_add_time u)

/-- The output register is bounded by the explicit space budget. -/
theorem ComputesInTimeAndSpace.output_size_le_space
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) : b.size ≤ s := by
  have hm := h.mass_le
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run (Cfg k Q) a n).reg_size_le_mass 0).trans (hm n)

/-- The output size is bounded by initial mass and the time budget. -/
theorem ComputesInTimeAndSpace.output_size_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace a b t s) :
    b.size ≤ (M.initInput (Config := Cfg k Q) a).mass + t := by
  have hm := h.mass_le_mass_add_time
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run (Cfg k Q) a n).reg_size_le_mass 0).trans (hm n)

theorem ComputesInTimeAndSpace.mono {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s t' s' : ℕ} (h : M.ComputesInTimeAndSpace a b t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesInTimeAndSpace a b t' s' :=
  Controller.computes_mono h ht hs

end Canonical

end Complexity.TreeMachine
