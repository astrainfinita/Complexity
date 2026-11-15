/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.StackMachine.Basic
public import Complexity.Resources.TuringMachine
public import Complexity.Resources.Nondeterministic.Basic
public import Complexity.Asymptotics.Nat
public import Complexity.Models.StackMachine.TuringMachine
public import Complexity.Models.StackMachine.FromTuringMachine
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Prod

/-!
# Resource bounds for simulations between stack and Turing machines

Both simulations are stated once on the behaviors of the generic models, for every choice shape
and interpretation (`TimeSpaceModel.exists_behavior_stackWith_of_tmWith`,
`TimeSpaceModel.exists_behavior_tmWith_of_stackWith`); the bridges for deterministic computations
and for nondeterministic decisions are read off from them.
-/

@[expose] public section

namespace Complexity

section Behaviors

variable {F : Type → Type*} {m : Type → Type*} [Functor F] [Monad m] [LawfulMonad m]
  [MonadLiftT F m] [LawfulFunctorLiftT F m] [MonadReturns m]
  {R : RawWord Bool → m (RawWord Bool) → ℕ → ℕ → Prop}

/-- Simulation by Boolean stacks keeps the time budget, and the stacks of every result use at
most twice the tape space visited by its source result. The outputs of the results correspond; on
`Multiset`, with multiplicities. -/
theorem TimeSpaceModel.exists_behavior_stackWith_of_tmWith
    (hR : R ∈ (TimeSpaceModel.tmWith F m).behaviors) :
    ∃ R' ∈ (TimeSpaceModel.stackWith F m).behaviors, ∀ x y t s, R x y t s → R' x y t (2 * s) := by
  obtain ⟨κ, hκ, Q, hQ, M, rfl⟩ := hR
  exact ⟨_, ⟨_, inferInstance, _, inferInstance, M.toStack, rfl⟩, fun _ _ _ _ h ↦
    TM.ComputesWithinWith.toStack (by rwa [Functor.map_map])⟩

/-- Simulation by Turing machines keeps the time budget, and each of the `c` tapes of every result
is bounded by the peak stack space of its source result plus its blank initial cell. -/
theorem TimeSpaceModel.exists_behavior_tmWith_of_stackWith
    (hR : R ∈ (TimeSpaceModel.stackWith F m).behaviors) :
    ∃ c, ∃ R' ∈ (TimeSpaceModel.tmWith F m).behaviors,
      ∀ x y t s, R x y t s → R' x y t (c * (s + 1)) := by
  obtain ⟨κ, hκ, Q, hQ, M, rfl⟩ := hR
  refine ⟨Fintype.card κ, _, ⟨κ, hκ, _, inferInstance, M.toTM, rfl⟩, fun _ _ _ _ h ↦ ?_⟩
  have := h.toTM
  rwa [Functor.map_map] at this

end Behaviors

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]
  {f : α → β} {p : α → Prop} {t s : α → ℕ}

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
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨c, R', hR', hR'R⟩ := TimeSpaceModel.exists_behavior_tmWith_of_stackWith hR
  exact ⟨c, R', hR', h.mono fun hrun => hR'R _ _ _ _ hrun⟩

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

/-- Simulation keeps the time budget of every branch; each of the `c` tapes of every branch is
bounded by the peak stack space of its own source branch plus its blank initial cell. The branch
outputs correspond one to one, with multiplicities. -/
theorem _root_.Complexity.TimeSpaceModel.NDecidableWithinByCode.toNTM
    {t s : α → RawWord Bool → ℕ} (h : TimeSpaceModel.nstack.NDecidableWithinByCode p t s) :
    ∃ c : ℕ, TimeSpaceModel.ntm.NDecidableWithinByCode p t (fun a r => c * (s a r + 1)) := by
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨c, R', hR', hR'R⟩ := TimeSpaceModel.exists_behavior_tmWith_of_stackWith hR
  exact ⟨c, R', hR', h.mono fun hrun => hR'R _ _ _ _ hrun⟩

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
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨R', hR', hR'R⟩ := TimeSpaceModel.exists_behavior_stackWith_of_tmWith hR
  exact ⟨R', hR', h.mono fun hrun => hR'R _ _ _ _ hrun⟩

theorem _root_.Complexity.TimeSpaceModel.ComputableWithin.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableWithin f t s) :
    TimeSpaceModel.stack.ComputableWithin f t (fun a => 2 * s a) :=
  TimeSpaceModel.ComputableWithinByCode.toStack_of_tm h

theorem _root_.Complexity.TimeSpaceModel.ComputableIn.toStack_of_tm
    (h : TimeSpaceModel.tm.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.stack.ComputableIn f IsO(t) IsO(s) := by
  obtain ⟨u, v, h, hu, hv⟩ := h
  exact ⟨_, _, TimeSpaceModel.ComputableWithin.toStack_of_tm h, hu, hv.const_mul_left 2⟩

/-- Simulation keeps the time budget of every branch; the Boolean stacks of every branch use at
most twice the tape space visited by its own source branch. The branch outputs correspond one to
one, with multiplicities. -/
theorem _root_.Complexity.TimeSpaceModel.NDecidableWithinByCode.toStack_of_ntm
    {t s : α → RawWord Bool → ℕ} (h : TimeSpaceModel.ntm.NDecidableWithinByCode p t s) :
    TimeSpaceModel.nstack.NDecidableWithinByCode p t (fun a r => 2 * s a r) := by
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨R', hR', hR'R⟩ := TimeSpaceModel.exists_behavior_stackWith_of_tmWith hR
  exact ⟨R', hR', h.mono fun hrun => hR'R _ _ _ _ hrun⟩

end TM
end InputBudgets

end Complexity
