/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.StackMachine.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Asymptotics.Nat
public import Complexity.Models.StackMachine.TuringMachine
public import Complexity.Models.StackMachine.FromTuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Prod

/-! # Resource bounds for simulations between stack and Turing machines -/

@[expose] public section

namespace Complexity

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]
  {f : α → β} {t s : α → ℕ}

namespace StackMachine

theorem Computes.toTM {κ : Type} [Fintype κ] {Q : Type}
    {M : StackMachine Id κ Bool Q} (h : Computes M f t s) :
    TM.Computes M.toTM f t (fun a => Fintype.card κ * (s a + 1)) :=
  Encoding.Computes.mono h (fun hc => hc.toTM)

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toTM
    (h : TimeSpaceModel.stack.ComputableWithin f t s) :
    ∃ c : ℕ, TimeSpaceModel.tm.ComputableWithin f t (fun a => c * (s a + 1)) := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableWithin_iff.mp h
  exact ⟨Fintype.card κ, h.toTM.computableWithin⟩

/-- Blank tape cells remain a real additive cost even after hiding multiplicative constants. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithGrowth.toTM
    (h : TimeSpaceModel.stack.ComputableWithGrowth f t s) :
    TimeSpaceModel.tm.ComputableWithGrowth f t (fun a => s a + 1) := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  obtain ⟨c, h⟩ := TimeSpaceModel.ComputableWithin.toTM h
  exact ⟨_, _, h, hu, (hv.add (Dominated.refl _)).const_mul_left c⟩

end StackMachine

namespace TM

theorem Computes.toStack {κ : Type} [Fintype κ] {Q : Type}
    {M : TM Id κ (Option Bool) Q} (h : Computes M f t s) :
    StackMachine.Computes M.toStack f t (fun a => 2 * s a) :=
  Encoding.Computes.mono h (fun hc => hc.toStack)

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableWithin f t s) :
    TimeSpaceModel.stack.ComputableWithin f t (fun a => 2 * s a) := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := computableWithin_iff.mp h
  exact h.toStack.computableWithin

theorem _root_.Complexity.TimeSpaceModel.ComputableWithGrowth.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableWithGrowth f t s) :
    TimeSpaceModel.stack.ComputableWithGrowth f t s := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨_, _, TimeSpaceModel.ComputableWithin.toStack_of_tm h, hu, hv.const_mul_left 2⟩

end TM
end InputBudgets

end Complexity
