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

`ComputesWithinWith` is the specification of this model for every choice shape and every
interpretation: `Controller.ComputesWithinCostWith` with the number of transitions as time and the
peak total work-stack length as space. In every interpretation, it follows from a step at which
every result has halted with its output, with the space bounded by the time
(`ComputesWithinWith.of_forall_halted`). The deterministic `ComputesWithin` is its instance on `Id`.
Build that one with `ComputesWithinWith.of_halted` and take it apart with
`ComputesWithinWith.exists_halted`; both are attached to the general specification, so dot notation
finds them on a `ComputesWithin` and also on a `ComputesWithinWith Id` that was not stated through
it. In the specifications the parameters `κ`, `Γ` and `Q` share one universe, because
`Controller.ComputesWithinCostWith` keeps outputs in the universe of the results; this is a current
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

/-- Compute in the interpretation `m` with transitions as time and the peak total work-stack
length as space: every history of the run stays within both budgets, and at some step every result
has halted with the corresponding output. -/
def ComputesWithinWith {F : Type u → Type*} (m : Type u → Type*) [Monad m] [MonadLiftT F m]
    [MonadReturns m] (M : StackMachine F κ Γ Q) (xs : List Γ) (outs : m (List Γ))
    (t s : ℕ) : Prop :=
  M.ComputesWithinCostWith m xs outs Controller.History.length (fun h ↦ h.configSup Cfg.mass) t s

/-- Enlarging budgets keeps the same outputs. -/
theorem ComputesWithinWith.mono {F : Type u → Type*} {m : Type u → Type*} [Monad m]
    [MonadLiftT F m] [MonadReturns m] {M : StackMachine F κ Γ Q} {xs : List Γ}
    {outs : m (List Γ)} {t s t' s' : ℕ} (h : M.ComputesWithinWith m xs outs t s)
    (ht : t ≤ t') (hs : s ≤ s') : M.ComputesWithinWith m xs outs t' s' :=
  Controller.computesWithinCostWith_mono h ht hs

/-- When every configuration that the run can return after `t` steps has halted with the output
`out` of that configuration, the machine computes the image of the run under `out`, within `t`
transitions and `Fintype.card κ * t` work-stack symbols. -/
theorem ComputesWithinWith.of_forall_halted {F : Type u → Type*} {m : Type u → Type*} [Monad m]
    [LawfulMonad m] [MonadLiftT F m] [MonadReturns m] (M : StackMachine F κ Γ Q) (xs : List Γ)
    {t : ℕ} (out : Q × Cfg κ Γ xs.toArray → List Γ)
    (h : ∀ c ∈ returns (M.runWith m xs t), M.Halted c ∧ c.2.output = (out c).toArray) :
    M.ComputesWithinWith m xs (out <$> M.runWith m xs t) t (Fintype.card κ * t) := by
  have hlen := M.length_le_of_forall_halted m xs fun c hc ↦ (h c hc).1
  refine ⟨fun p hp ↦ ⟨(Controller.History.length_snd p).trans_le (hlen p hp), ?_⟩, t, ?_⟩
  · refine (configSup_mass_le p.snd).trans ?_
    rw [Controller.History.first_snd, Controller.first_eq_of_mem_histories hp, Controller.init_snd,
      hasConfig_init, Cfg.mass_init, Nat.zero_add, Controller.History.length_snd]
    exact Nat.mul_le_mul_left _ (hlen p hp)
  · have hr := LiftRel.map_map (M.runWith m xs t) (R := fun c y ↦ y = out c) (f := id) fun _ ↦ rfl
    rw [id_map] at hr
    exact hr.mono_of_mem fun c hc y hy ↦ hy ▸ h c hc

/-- The run halts with the output, and its transitions and peak total work-stack length stay
within budget at every depth. -/
def ComputesWithin (M : StackMachine Id κ Γ Q) (xs ys : List Γ) (t s : ℕ) : Prop :=
  M.ComputesWithinWith Id xs (pure ys) t s

/-- Bounds at a halting step are enough: length and the peak work-stack mass grow along the run. -/
theorem ComputesWithinWith.of_halted {M : StackMachine Id κ Γ Q} {xs ys : List Γ} {t s : ℕ}
    (n : ℕ) (hh : M.Halted (M.run xs n)) (ho : (M.run xs n).2.output = ys.toArray)
    (ht : (M.runHistory xs n).snd.length ≤ t)
    (hs : (M.runHistory xs n).snd.configSup Cfg.mass ≤ s) :
    M.ComputesWithinWith Id xs (pure ys) t s :=
  Controller.ComputesWithinCost.of_halted (fun _ _ ↦ M.length_runHistory_mono _)
    (fun _ _ ↦ M.configSup_runHistory_mono _ _) n hh ho ht hs

/-- The halting step of a computation, with the output and both measurements within budget. -/
theorem ComputesWithinWith.exists_halted {M : StackMachine Id κ Γ Q} {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesWithinWith Id xs (pure ys) t s) :
    ∃ n, M.Halted (M.run xs n) ∧ (M.run xs n).2.output = ys.toArray ∧
      (M.runHistory xs n).snd.length ≤ t ∧ (M.runHistory xs n).snd.configSup Cfg.mass ≤ s :=
  Controller.ComputesWithinCost.exists_halted h

/-- Initially empty work stacks grow by at most one symbol per stack per transition. -/
theorem ComputesWithin.of_run {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {n t : ℕ}
    (hh : M.Halted (M.run xs n))
    (ho : (M.run xs n).2.output = ys.toArray) (hn : n ≤ t) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) :=
  (ComputesWithinWith.of_forall_halted M xs (fun _ ↦ ys) fun _ hc ↦
    Id.mem_returns.1 hc ▸ ⟨hh, ho⟩).mono hn (Nat.mul_le_mul_left _ hn)

/-- Read the halted result at the advertised transition budget. -/
theorem ComputesWithin.run_spec {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.Halted (M.run xs t) ∧ (M.run xs t).2.output = ys.toArray := by
  have ⟨hh, ho, _⟩ := Controller.computesWithinCost_unit_iff.mp h
  exact ⟨hh, ho⟩

theorem ComputesWithin.space_of_time {M : StackMachine Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.ComputesWithin xs ys t (Fintype.card κ * t) :=
  .of_run h.run_spec.1 h.run_spec.2 le_rfl

end Complexity.StackMachine
