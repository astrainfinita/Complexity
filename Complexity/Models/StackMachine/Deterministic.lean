/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Transition time and peak work-stack space

In the specification `ComputesWithin` the parameters `κ`, `Γ` and `Q` share one universe, because
`Controller.ComputesInWith` keeps outputs in the universe of the results; this is a current
limitation, not a decision.
-/

@[expose] public section

universe u

namespace Complexity.StackMachine

section Mass

variable {κ Γ : Type*} [Fintype κ]

/-- The total number of symbols on the work stacks, excluding input and output. -/
def Cfg.mass {xs : Array Γ} (c : Cfg κ Γ xs) : ℕ :=
  ∑ i, (c.stacks i).length

theorem Cfg.mass_apply_le {xs : Array Γ} (c : Cfg κ Γ xs) (a : Action κ Γ) :
    (apply a c).mass ≤ c.mass + Fintype.card κ := by
  calc
    (apply a c).mass ≤ ∑ i, ((c.stacks i).length + 1) := by
      apply Finset.sum_le_sum
      intro i _
      cases h : a.work i <;> simp [h, Op.apply]
      omega
    _ = c.mass + Fintype.card κ := by simp [Cfg.mass, Finset.sum_add_distrib]

theorem configSup_mass_le {xs : Array Γ} (h : Controller.History (Cfg κ Γ xs) (Action κ Γ)) :
    h.configSup Cfg.mass ≤ h.first.mass + Fintype.card κ * h.length := by
  simpa only [Controller.History.actionSum_const, Nat.mul_comm] using h.configSup_le_add_actionSum
    Cfg.mass (fun _ _ ↦ Fintype.card κ) (fun a c _ ↦ c.mass_apply_le a)

@[simp] theorem Cfg.mass_init (xs : List Γ) : (Cfg.init κ xs).mass = 0 := by
  simp [Cfg.mass]

end Mass

variable {κ Γ Q : Type u} [Fintype κ]

/-- The run halts with the output, and its transitions and peak total work-stack length stay
within budget at every depth. -/
def ComputesWithin (M : StackMachine Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) : Prop :=
  M.ComputesIn xs ys Controller.History.length (fun h ↦ h.configSup Cfg.mass) t s

/-- Bounds at a halting step are enough: length and the peak work-stack mass grow along the run. -/
theorem ComputesWithin.of_halted {M : StackMachine Id κ Γ Q} {xs ys : List Γ} {t s : ℕ} (n : ℕ)
    (hh : M.Halted (M.run xs n)) (ho : (M.run xs n).2.output = ys.toArray)
    (ht : (M.runHistory xs n).snd.length ≤ t)
    (hs : (M.runHistory xs n).snd.configSup Cfg.mass ≤ s) :
    M.ComputesWithin xs ys t s :=
  Controller.ComputesIn.of_halted (fun _ _ ↦ M.length_runHistory_mono _)
    (fun _ _ ↦ M.configSup_runHistory_mono _ _) n hh ho ht hs

/-- Initially empty work stacks grow by at most one symbol per stack per transition. -/
theorem ComputesWithin.of_run {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {n t : ℕ}
    (hh : M.Halted (M.run xs n))
    (ho : (M.run xs n).2.output = ys.toArray) (hn : n ≤ t) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) := by
  have ht := (M.length_runHistory_le xs n).trans hn
  refine .of_halted n hh ho ((Controller.History.length_snd _).trans_le ht)
    ((configSup_mass_le _).trans ?_)
  simpa [Controller.runHistory, Controller.History.first_snd,
      Controller.History.length_snd] using Nat.mul_le_mul_left (Fintype.card κ) ht

/-- Read the halted result at the advertised transition budget. -/
theorem ComputesWithin.run_spec {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.Halted (M.run xs t) ∧ (M.run xs t).2.output = ys.toArray := by
  have ⟨hh, ho, _⟩ := Controller.computesIn_unit_iff.mp h
  exact ⟨hh, ho⟩

theorem ComputesWithin.space_of_time {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) :=
  .of_run h.run_spec.1 h.run_spec.2 le_rfl

theorem ComputesWithin.mono {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s t' s' : ℕ} (h : M.ComputesWithin xs ys t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesWithin xs ys t' s' :=
  Controller.computesIn_mono h ht hs

end Complexity.StackMachine
