/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.StackMachine.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Models.StackMachine.TuringMachine
public import Complexity.Models.StackMachine.FromTuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Prod

/-! # Resource bounds for simulations between stack and Turing machines -/

@[expose] public section

namespace Complexity

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

namespace StackMachine

/-- The same finite machine computes every encoded input within the source time bound.
The target space bound depends on the number of source stacks. -/
theorem Computes.toTM {κ : Type} [Fintype κ] {Q : Type}
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) :
    TM.Computes M.toTM f t
      (fun n ↦ Fintype.card κ * (s n + 1)) := by
  intro xs a ha
  obtain ⟨ys, hy, hc⟩ := h xs a ha
  exact ⟨ys, hy, hc.toTM⟩

/-- The finite stack count becomes a constant in the target space bound. -/
theorem computableInTimeAndSpace_toTM {f : α → β} {t s : ℕ → ℕ}
    (h : TimeSpaceModel.stack.ComputableInTimeAndSpace f t s) :
    ∃ c : ℕ, TimeSpaceModel.tm.ComputableInTimeAndSpace f t
      (fun n ↦ c * (s n + 1)) := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  exact ⟨Fintype.card κ, h.toTM.computableInTimeAndSpace⟩

end StackMachine

namespace TM

/-- Four bit stacks per tape preserve transitions and use at most twice the visited space. -/
theorem Computes.toStack {κ : Type} [Fintype κ] {Q : Type}
    {M : TM Id κ (Option Bool) Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) :
    StackMachine.Computes M.toStack f t (fun n ↦ 2 * s n) := by
  intro xs a ha
  obtain ⟨ys, hy, hc⟩ := h xs a ha
  exact ⟨ys, hy, hc.toStack⟩

/-- Finite Turing computations have native stack realizations with linear space. -/
theorem computableInTimeAndSpace_toStack {f : α → β} {t s : ℕ → ℕ}
    (h : TimeSpaceModel.tm.ComputableInTimeAndSpace f t s) :
    TimeSpaceModel.stack.ComputableInTimeAndSpace f t (fun n ↦ 2 * s n) := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  exact h.toStack.computableInTimeAndSpace

end TM
end Complexity
