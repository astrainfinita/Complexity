/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Cost

/-!
# Deterministic tree machines and resource bounds

History length counts active transitions; action sums charge source reads and result construction.
The generic controller space measure records the largest total expanded tree size seen so far.
All three ignore halted padding.
The cumulative cost bounds time and, together with initial mass, every intermediate mass.
It is bounded above by the unit time multiplied by the peak register mass.
A running `nop` costs one and preserves the register bank.
-/

@[expose] public section

namespace Complexity.TreeMachine

open Controller (History)

variable {k : ℕ} {Q : Type*}

theorem Cfg.mass_init_le [NeZero k] (a : Tree) : (Cfg.init k a).mass ≤ a.size + k := by
  change (∑ j, (input 0 a j).size) ≤ _
  rw [sum_size_input]
  omega

theorem configSup_mass_le (M : TreeMachine Id k Q) (c : Q × Cfg k) (t : ℕ) :
    (M.runHistoryFrom c t).snd.configSup Cfg.mass ≤
      c.2.mass + (M.runHistoryFrom c t).snd.actionSum Action.sizeCost := by
  simpa only [History.first_snd, Controller.first_runHistoryFrom] using
    (M.runHistoryFrom c t).snd.configSup_le_add_actionSum Cfg.mass
      Action.sizeCost (fun o c _ ↦ c.mass_apply_le o)

theorem mass_runFrom_le (M : TreeMachine Id k Q) (c : Q × Cfg k) {s t : ℕ} (h : s ≤ t) :
    (M.runFrom c s).2.mass ≤
      c.2.mass + (M.runHistoryFrom c t).snd.actionSum Action.sizeCost :=
  ((M.config_le_configSup_runHistoryFrom (Cfg.mass ∘ Prod.snd) c h).trans_eq
    (History.configSup_snd _ _).symm).trans (M.configSup_mass_le c t)

section Canonical

variable [NeZero k]

/-- The computation eventually reaches a halting state. -/
def Terminates (M : TreeMachine Id k Q) (a : Tree) : Prop :=
  ∃ t, M.Halted (M.run a t)

/-- The first halting time, with the same convention as for a multi-tape machine. -/
def HaltsAt (M : TreeMachine Id k Q) (a : Tree) (t : ℕ) : Prop :=
  M.Halted (M.run a t) ∧ ∀ u < t, ¬M.Halted (M.run a u)

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
    (h : M.Halted (M.run a t)) : ∃ n ≤ t, M.HaltsAt a n := by
  classical
  have h' : M.Terminates a := ⟨t, h⟩
  exact ⟨Nat.find h', Nat.find_min' h' h, Nat.find_spec h',
    fun _ hn ↦ Nat.find_min h' hn⟩

theorem Terminates.exists_haltsAt {M : TreeMachine Id k Q} {a : Tree}
    (h : M.Terminates a) : ∃ t, M.HaltsAt a t := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨n, _, hn⟩ := M.exists_haltsAt_le a ht
  exact ⟨n, hn⟩

theorem HaltsAt.le_actionSum {M : TreeMachine Id k Q} {a : Tree} {t : ℕ}
    (h : M.HaltsAt a t) :
    t ≤ (M.runHistory a t).snd.actionSum Action.sizeCost :=
  (M.length_runHistoryFrom_eq _ _ h.2).symm.trans_le
    ((History.length_snd _).symm.trans_le (length_le_actionSum _))

/-- Every finite prefix stays within the given expanded-tree space bound. -/
def UsesSpace (M : TreeMachine Id k Q) (a : Tree) (s : ℕ) : Prop :=
  ∀ t, (M.runHistory a t).snd.configSup Cfg.mass ≤ s

/-- Compute a tree in register zero within a cumulative size-charge time budget
and a maximum expanded-tree space budget. The transition count is an existential witness,
since the external time charge depends on the trees read or constructed. -/
def ComputesWithin (M : TreeMachine Id k Q) (a : Tree)
    (b : Tree) (t s : ℕ) : Prop :=
  M.ComputesWith a b (fun h ↦ h.snd.actionSum Action.sizeCost)
    (fun h ↦ h.snd.configSup Cfg.mass) t s

/-- Compute with one unit per active transition and peak expanded-tree space. -/
def ComputesInUnitTimeAndSpace (M : TreeMachine Id k Q) (a b : Tree) (t s : ℕ) : Prop :=
  M.ComputesWith a b History.length (fun h ↦ h.snd.configSup Cfg.mass) t s

/-- Switching to unit charges preserves both advertised bounds on the same run. -/
theorem ComputesWithin.toUnitTime {M : TreeMachine Id k Q} {a b : Tree}
    {t s : ℕ} (h : M.ComputesWithin a b t s) :
    M.ComputesInUnitTimeAndSpace a b t s := by
  obtain ⟨n, hh, ho, ht, hs⟩ := h
  exact ⟨n, hh, ho,
    ((History.length_snd _).symm.trans_le (length_le_actionSum _)).trans ht, hs⟩

/-- A bound on all intermediate register trees permits size charging on the same run. -/
theorem ComputesInUnitTimeAndSpace.toSizeCost {M : TreeMachine Id k Q} {a b : Tree}
    {t s : ℕ} (h : M.ComputesInUnitTimeAndSpace a b t s) :
    M.ComputesWithin a b (t * s) s := by
  obtain ⟨n, hh, ho, ht, hs⟩ := h
  refine ⟨n, hh, ho, (actionSum_le_length_mul_mass _).trans ?_, hs⟩
  rw [History.length_snd]
  exact Nat.mul_le_mul ht hs

theorem ComputesInUnitTimeAndSpace.mono {M : TreeMachine Id k Q} {a b : Tree}
    {t s t' s' : ℕ} (h : M.ComputesInUnitTimeAndSpace a b t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesInUnitTimeAndSpace a b t' s' :=
  Controller.computesWith_mono h ht hs

/-- A halted run's time budget also bounds its peak space by input size and register count. -/
theorem ComputesWithin.of_run {M : TreeMachine Id k Q} {a b : Tree} {n t s : ℕ}
    (hh : M.Halted (M.run a n))
    (ho : (M.run a n).2.regs 0 = b)
    (ht : (M.runHistory a n).snd.actionSum Action.sizeCost ≤ t)
    (hs : a.size + k + t ≤ s) :
    M.ComputesWithin a b t s := by
  refine ⟨n, hh, ho, ht, ?_⟩
  exact (M.configSup_mass_le _ n).trans
    ((Nat.add_le_add (Cfg.mass_init_le a) ht).trans hs)

/-- Replace a computation's space budget with the bound supplied by its time cost. -/
theorem ComputesWithin.space_of_time {M : TreeMachine Id k Q} {a b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) :
    M.ComputesWithin a b t (a.size + k + t) := by
  obtain ⟨n, hh, ho, ht, _⟩ := h
  exact .of_run hh ho ht le_rfl

theorem ComputesWithin.terminates {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesWithin a b t s) :
    M.Terminates a := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, hn⟩

/-- The witness can be chosen to be the first halting time, which is at most the time budget. -/
theorem ComputesWithin.exists_haltsAt {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesWithin a b t s) :
    ∃ n ≤ t, M.HaltsAt a n ∧ (M.run a n).2.regs 0 = b ∧
      (M.runHistory a n).snd.actionSum Action.sizeCost ≤ t ∧
      (M.runHistory a n).snd.configSup Cfg.mass ≤ s := by
  obtain ⟨u, hu, ha, ht, hs⟩ := h
  change (M.run a u).2.regs 0 = b at ha
  obtain ⟨n, hn, hh⟩ := M.exists_haltsAt_le a hu
  have hc : (M.runHistory a n).snd.actionSum Action.sizeCost ≤ t := by
    simp only [History.actionSum_snd] at ht ⊢
    exact (M.actionSum_runHistory_mono a _ hn).trans ht
  refine ⟨n, hh.le_actionSum.trans hc, hh, ?_, hc, ?_⟩
  · rwa [M.run_eq_of_halted a hh.1 hn] at ha
  · simp only [History.configSup_snd] at hs ⊢
    exact (M.configSup_runHistory_mono a _ hn).trans hs

/-- A terminating bounded computation controls space along the entire padded execution. -/
theorem ComputesWithin.usesSpace {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesWithin a b t s) :
    M.UsesSpace a s :=
  Controller.computesWith_space_le h fun _ _ hn ↦ by
    simpa only [History.configSup_snd] using M.configSup_runHistory_mono a _ hn

theorem ComputesWithin.actionSum_le {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesWithin a b t s)
    (u : ℕ) : (M.runHistory a u).snd.actionSum Action.sizeCost ≤ t := by
  simp only [ComputesWithin, History.actionSum_snd] at h ⊢
  exact Controller.computesWith_actionSum_le h u

/-- The time budget controls space even without using the explicit space budget. -/
theorem ComputesWithin.configSup_mass_le_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) (u : ℕ) :
    (M.runHistory a u).snd.configSup Cfg.mass ≤ (Cfg.init k a).mass + t :=
  (M.configSup_mass_le _ u).trans (Nat.add_le_add_left (h.actionSum_le u) _)

theorem ComputesWithin.mass_le {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s : ℕ} (h : M.ComputesWithin a b t s)
    (u : ℕ) : (M.run a u).2.mass ≤ s :=
  ((M.config_le_configSup_runHistory a (Cfg.mass ∘ Prod.snd : Q × Cfg k → ℕ)
    (Nat.le_refl u)).trans_eq
    (History.configSup_snd _ _).symm).trans (h.usesSpace u)

theorem ComputesWithin.mass_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) (u : ℕ) :
    (M.run a u).2.mass ≤ (Cfg.init k a).mass + t :=
  ((M.config_le_configSup_runHistory a (Cfg.mass ∘ Prod.snd : Q × Cfg k → ℕ)
    (Nat.le_refl u)).trans_eq
    (History.configSup_snd _ _).symm).trans (h.configSup_mass_le_add_time u)

/-- The initial input register is bounded by the explicit space budget. -/
theorem ComputesWithin.input_size_le_space
    {M : TreeMachine Id k Q} {a b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) : a.size ≤ s := by
  have hi := (Cfg.init k a).reg_size_le_mass 0
  simpa using hi.trans (h.mass_le 0)

/-- The output register is bounded by the explicit space budget. -/
theorem ComputesWithin.output_size_le_space
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) : b.size ≤ s := by
  have hm := h.mass_le
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run a n).2.reg_size_le_mass 0).trans (hm n)

/-- The output size is bounded by initial mass and the time budget. -/
theorem ComputesWithin.output_size_le_mass_add_time
    {M : TreeMachine Id k Q} {a : Tree} {b : Tree} {t s : ℕ}
    (h : M.ComputesWithin a b t s) :
    b.size ≤ (Cfg.init k a).mass + t := by
  have hm := h.mass_le_mass_add_time
  obtain ⟨n, _, ha, _, _⟩ := h
  rw [← ha]
  exact ((M.run a n).2.reg_size_le_mass 0).trans (hm n)

theorem ComputesWithin.mono {M : TreeMachine Id k Q} {a : Tree}
    {b : Tree} {t s t' s' : ℕ} (h : M.ComputesWithin a b t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesWithin a b t' s' :=
  Controller.computesWith_mono h ht hs

end Canonical

end Complexity.TreeMachine
