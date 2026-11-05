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

/-- Simulation keeps the time budget; each of the `c` tapes is bounded by the peak stack
space plus its blank initial cell. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithinByCode.toTM
    {t s : α → RawWord Bool → ℕ} (h : TimeSpaceModel.stack.ComputableWithinByCode f t s) :
    ∃ c : ℕ, TimeSpaceModel.tm.ComputableWithinByCode f t (fun a r => c * (s a r + 1)) := by
  obtain ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩ := h
  exact ⟨Fintype.card κ, _, ⟨κ, hκ, _, inferInstance, M.toTM, rfl⟩, h.mono fun hc => hc.toTM⟩

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toTM
    (h : TimeSpaceModel.stack.ComputableWithin f t s) :
    ∃ c : ℕ, TimeSpaceModel.tm.ComputableWithin f t (fun a => c * (s a + 1)) :=
  TimeSpaceModel.ComputableWithinByCode.toTM h

/-- Blank tape cells remain a real additive cost even after hiding multiplicative constants. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableIn.toTM
    (h : TimeSpaceModel.stack.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.tm.ComputableIn f IsO(t) IsO(fun a => s a + 1) := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  obtain ⟨c, h⟩ := TimeSpaceModel.ComputableWithin.toTM h
  exact ⟨_, _, h, hu, (hv.add (Dominated.refl _)).const_mul_left c⟩

end StackMachine

namespace TM

theorem Computes.toStack {κ : Type} [Fintype κ] {Q : Type}
    {M : TM Id κ (Option Bool) Q} (h : Computes M f t s) :
    StackMachine.Computes M.toStack f t (fun a => 2 * s a) :=
  Encoding.Computes.mono h (fun hc => hc.toStack)

/-- Simulation keeps the time budget; the Boolean stacks use at most twice the visited
tape space. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithinByCode.toStack_of_tm
    {t s : α → RawWord Bool → ℕ} (h : TimeSpaceModel.tm.ComputableWithinByCode f t s) :
    TimeSpaceModel.stack.ComputableWithinByCode f t (fun a r => 2 * s a r) := by
  obtain ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩ := h
  exact ⟨_, ⟨_, inferInstance, _, inferInstance, M.toStack, rfl⟩, h.mono fun hc => hc.toStack⟩

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableWithin f t s) :
    TimeSpaceModel.stack.ComputableWithin f t (fun a => 2 * s a) :=
  TimeSpaceModel.ComputableWithinByCode.toStack_of_tm h

theorem _root_.Complexity.TimeSpaceModel.ComputableIn.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.stack.ComputableIn f IsO(t) IsO(s) := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨_, _, TimeSpaceModel.ComputableWithin.toStack_of_tm h, hu, hv.const_mul_left 2⟩

end TM
end InputBudgets

end Complexity
