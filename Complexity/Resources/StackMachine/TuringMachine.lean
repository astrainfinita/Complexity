/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.StackMachine.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Models.StackMachine.TuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum

/-! # Resource bounds for the stack-to-tape simulation -/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- The same finite machine computes every encoded input with twice the time.
The target space bound depends on the number of source stacks. -/
theorem Computes.toTM {κ : Type} [Fintype κ] {Q : Type}
    {M : StackMachine Id κ Bool Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) :
    TM.Computes M.toTM f (fun n ↦ 2 * t n)
      (fun n ↦ Fintype.card κ * (2 * t n + 1)) := by
  rw [TM.computes_iff]
  intro xs a ha
  obtain ⟨ys, hy, hc⟩ := h xs a ha
  exact ⟨ys, hy, hc.toTM⟩

/-- Hiding the finite stack count preserves the linear time bound. -/
theorem computableInTime_toTM {f : α → β} {t : ℕ → ℕ}
    (h : timeSpaceModel.ComputableInTime f t) :
    TM.timeSpaceModel.ComputableInTime f (fun n ↦ 2 * t n) := by
  obtain ⟨s, h⟩ := h
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  exact h.toTM.computableInTimeAndSpace.computableInTime

end Complexity.StackMachine
