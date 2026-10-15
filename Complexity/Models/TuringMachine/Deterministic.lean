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
Termination and bounds on all execution prefixes are separate properties.
-/

@[expose] public section

namespace Complexity.TM

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- The computation eventually reaches a halting state. -/
def Terminates (M : TM Id κ Γ Q) (xs : List Γ) : Prop :=
  ∃ t, M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs t)

/-- The first halting time, excluding the identity steps that pad a halted execution. -/
def HaltsAt (M : TM Id κ Γ Q) (xs : List Γ) (t : ℕ) : Prop :=
  M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs t) ∧
    ∀ u < t, ¬M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs u)

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
  ∀ t, (M.runHistory (Cfg κ Γ Q xs.toArray) xs t).space ≤ s

/-- Compute with unit action time and visited-cell space on one execution history. -/
def ComputesWithin [Fintype κ] (M : TM Id κ Γ Q) (xs ys : List Γ)
    (t s : ℕ) : Prop :=
  M.ComputesWith (Config := Cfg κ Γ Q xs.toArray)
    Controller.History.length Controller.History.space xs ys t s

theorem ComputesWithin.mono [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s t' s' : ℕ}
    (h : M.ComputesWithin xs ys t s) (ht : t ≤ t') (hs : s ≤ s') :
    M.ComputesWithin xs ys t' s' :=
  Controller.computesWith_mono h ht hs

/-- Unit-time computation visits at most one new cell per tape per transition. -/
theorem ComputesWithin.space_of_time [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.ComputesWithin xs ys t (Fintype.card κ * (t + 1)) := by
  obtain ⟨n, hh, ho, ht, _⟩ := h
  exact ⟨n, hh, ho, ht, (Controller.History.space_le_length _).trans
    (Nat.mul_le_mul_left _ (Nat.succ_le_succ ht))⟩

/-- Read the ordinary run's result without carrying its visitation history. -/
theorem ComputesWithin.run_spec [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ} (h : M.ComputesWithin xs ys t s) :
    M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs t) ∧
      (M.run (Cfg κ Γ Q xs.toArray) xs t).output = ys.toArray := by
  have ⟨hh, ho, _⟩ := Controller.computesWith_unit_iff.mp h
  simpa only [rawExecution_hasOutput] using And.intro hh ho

theorem ComputesWithin.terminates [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesWithin xs ys t s) : M.Terminates xs :=
  ⟨t, h.run_spec.1⟩

/-- A terminating bounded computation controls space along the entire infinite padded run. -/
theorem ComputesWithin.usesSpace [Fintype κ] {M : TM Id κ Γ Q}
    {xs ys : List Γ} {t s : ℕ}
    (h : M.ComputesWithin xs ys t s) : M.UsesSpace xs s :=
  fun u ↦ Controller.computesWith_space_le h (M.runHistoryFrom_space_mono _) u

end Complexity.TM
