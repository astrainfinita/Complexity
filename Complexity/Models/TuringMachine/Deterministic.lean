/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Cost

/-!
# Deterministic execution and resource bounds

These definitions specialize the choice shape to `Id`. Space counts visited work cells,
including the initial head positions and blank cells, and excludes input and output.
`ComputesWithin` is `ComputesWithinWith` on `Id`: it bounds length and space at every depth of the
run, including the halted padding; both grow along the run, so the bounds at a halting step are
enough. Build it with `ComputesWithinWith.of_halted` and take it apart with
`ComputesWithinWith.exists_halted`. Both are attached to the general specification, so dot
notation finds them on a `ComputesWithin` and also on a `ComputesWithinWith Id` that was not stated
through it. The parameters `κ`, `Γ` and `Q` share one universe, because
`Controller.ComputesWithinCostWith` keeps outputs in the universe of the results; this is a current
limitation, not a decision.
-/

@[expose] public section

universe u

namespace Complexity.TM

variable {κ Γ Q : Type u} [Inhabited Γ] {xs : Array Γ}

/-- Compute with unit action time and visited-cell space: the run halts with the output, and both
measurements stay within budget at every depth. -/
def ComputesWithin [Fintype κ] (M : TM Id κ Γ Q) (xs ys : List Γ)
    (t s : ℕ) : Prop :=
  M.ComputesWithinWith Id xs (pure ys) t s

/-- Bounds at a halting step are enough: length and visited space grow along the run. -/
theorem ComputesWithinWith.of_halted [Fintype κ] {M : TM Id κ Γ Q} {xs ys : List Γ} {t s : ℕ}
    (n : ℕ) (hh : M.Halted (M.run xs n)) (ho : (M.run xs n).2.output = ys.toArray)
    (ht : (M.runHistory xs n).snd.length ≤ t) (hs : (M.runHistory xs n).snd.space ≤ s) :
    M.ComputesWithinWith Id xs (pure ys) t s :=
  Controller.ComputesWithinCost.of_halted (fun _ _ ↦ M.length_runHistory_mono _)
    (M.runHistoryFrom_space_mono _) n hh ho ht hs

/-- The halting step of a computation, with the output and both measurements within budget. -/
theorem ComputesWithinWith.exists_halted [Fintype κ] {M : TM Id κ Γ Q} {xs ys : List Γ}
    {t s : ℕ} (h : M.ComputesWithinWith Id xs (pure ys) t s) :
    ∃ n, M.Halted (M.run xs n) ∧ (M.run xs n).2.output = ys.toArray ∧
      (M.runHistory xs n).snd.length ≤ t ∧ (M.runHistory xs n).snd.space ≤ s :=
  Controller.ComputesWithinCost.exists_halted h

/-- A run visits at most one new cell per tape per transition. -/
theorem ComputesWithin.of_run [Fintype κ] {M : TM Id κ Γ Q} {xs ys : List Γ} {n t : ℕ}
    (hh : M.Halted (M.run xs n)) (ho : (M.run xs n).2.output = ys.toArray) (hn : n ≤ t) :
    M.ComputesWithin xs ys t (Fintype.card κ * (t + 1)) := by
  have ht := (Controller.History.length_snd _).trans_le ((M.length_runHistory_le xs n).trans hn)
  exact .of_halted n hh ho ht
    ((Controller.History.space_le_length _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ ht)))

/-- Read the ordinary run's result without carrying its visitation history. -/
theorem ComputesWithin.run_spec [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.Halted (M.run xs t) ∧ (M.run xs t).2.output = ys.toArray := by
  have ⟨hh, ho, _⟩ := Controller.computesWithinCost_unit_iff.mp h
  simpa only [hasOutput_isOutput] using And.intro hh ho

/-- Unit-time computation visits at most one new cell per tape per transition. -/
theorem ComputesWithin.space_of_time [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.ComputesWithin xs ys t (Fintype.card κ * (t + 1)) :=
  .of_run h.run_spec.1 h.run_spec.2 le_rfl

theorem ComputesWithin.terminates [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesWithin xs ys t s) : M.Terminates xs :=
  ⟨t, h.run_spec.1⟩

/-- A terminating bounded computation controls space along the entire infinite padded run. -/
theorem ComputesWithin.space_le [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesWithin xs ys t s) (u : ℕ) : (M.runHistory xs u).snd.space ≤ s :=
  Controller.computesWithinCost_space_le h u

end Complexity.TM
