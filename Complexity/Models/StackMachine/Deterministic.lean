/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Transition time and peak work-stack space -/

@[expose] public section

namespace Complexity.StackMachine

variable {κ Γ Q : Type*} [Fintype κ]

/-- The total number of symbols on the work stacks, excluding input and output. -/
def Cfg.mass {xs : Array Γ} (c : Cfg κ Γ Q xs) : ℕ :=
  ∑ i, (c.stacks i).length

theorem Cfg.mass_apply_le {xs : Array Γ} (c : Cfg κ Γ Q xs) (a : Action κ Γ Q) :
    (apply a c).mass ≤ c.mass + Fintype.card κ := by
  calc
    (apply a c).mass ≤ ∑ i, ((c.stacks i).length + 1) := by
      apply Finset.sum_le_sum
      intro i _
      cases h : a.work i <;> simp [h, Op.apply]
      omega
    _ = c.mass + Fintype.card κ := by simp [Cfg.mass, Finset.sum_add_distrib]

theorem configSup_mass_le {xs : Array Γ} (h : Controller.History (Cfg κ Γ Q xs)
    (Action κ Γ Q)) :
    h.configSup Cfg.mass ≤ h.first.mass + Fintype.card κ * h.length := by
  simpa only [Controller.History.actionSum_const, Nat.mul_comm] using h.configSup_le_add_actionSum
    Cfg.mass (fun _ _ ↦ Fintype.card κ) (fun a c _ ↦ c.mass_apply_le a)

@[simp] theorem mass_initInput (M : StackMachine Id κ Γ Q) (xs : List Γ) :
    (M.initInput (Config := Cfg κ Γ Q xs.toArray) xs).mass = 0 := by
  simp [Cfg.mass, Controller.initInput]

/-- One terminating history bounds transitions and the peak total work-stack length. -/
def ComputesWithin (M : StackMachine Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) : Prop :=
  M.ComputesWith (Config := Cfg κ Γ Q xs.toArray)
    Controller.History.length (fun h ↦ h.configSup Cfg.mass) xs ys t s

/-- Initially empty work stacks grow by at most one symbol per stack per transition. -/
theorem ComputesWithin.of_run {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {n t : ℕ}
    (hh : M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs n))
    (ho : (M.run (Cfg κ Γ Q xs.toArray) xs n).output = ys.toArray) (hn : n ≤ t) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) := by
  have ht := (M.length_runHistory_le (Cfg κ Γ Q xs.toArray) xs n).trans hn
  refine ⟨n, hh, ho, ht, ?_⟩
  exact (configSup_mass_le _).trans
    (by simpa [Controller.runHistory] using Nat.mul_le_mul_left (Fintype.card κ) ht)

/-- Read the halted result at the advertised transition budget. -/
theorem ComputesWithin.run_spec {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs t) ∧
      (M.run (Cfg κ Γ Q xs.toArray) xs t).output = ys.toArray := by
  have ⟨hh, ho, _⟩ := Controller.computesWith_unit_iff.mp h
  exact ⟨hh, ho⟩

theorem ComputesWithin.space_of_time {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) :=
  .of_run h.run_spec.1 h.run_spec.2 le_rfl

theorem ComputesWithin.mono {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s t' s' : ℕ} (h : M.ComputesWithin xs ys t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesWithin xs ys t' s' :=
  Controller.computesWith_mono h ht hs

end Complexity.StackMachine
