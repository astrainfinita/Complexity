/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine.Basic
public import Complexity.Resources.StackMachine.Basic
public import Complexity.Models.TreeMachine.Simulation.Correctness
public import Mathlib.Data.Fintype.EquivFin

/-! # Serialized tree computations on stack machines -/

@[expose] public section

namespace Complexity.TreeMachine

open Simulation

section InputBudgets

variable {α β : Type*} [e : Encoding Tree α] [Encoding Tree β]

/-- Serialization keeps budgets indexed by the source input. Loading still costs the
actual tree size, even when the chosen time budget is zero; the space budget bounds that
size because tree space counts the input. -/
theorem Computes.toStack {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]
    {M : TreeMachine Id k Q} {f : α → β} {t s : α → ℕ} (h : Computes M f t s) :
    StackMachine.Computes (compiler M) f
      (fun a => timeBound k (s a) (t a)) (fun a => spaceBound k (s a)) :=
  h.toRawWord fun hrun => (computesWithin M hrun).mono (by
    have := hrun.input_size_le_space
    simp only [timeBound]
    omega) le_rfl

/-- A serialized code is as long as its tree, so code-size budgets transfer directly.
Tree codes have positive size, which absorbs the simulator's fixed setup cost; the real
input-loading cost remains. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithinBySize.toStack_of_tree
    {f : α → β} {t s : ℕ → ℕ}
    (h : TimeSpaceModel.sizeCostTree.ComputableWithinBySize f t s) :
    ∃ c : ℕ, TimeSpaceModel.stack.ComputableWithinBySize f
      (fun n => c * (t n + n)) (fun n => c * s n) := by
  classical
  obtain ⟨R, ⟨k, hk, Q, hQ, M, rfl⟩, h⟩ := h
  let : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  refine ⟨42 * (k + 4) + 1, _, ⟨_, inferInstance, _, inferInstance, compiler M, rfl⟩,
    h.toRawWord fun {_ x _} hrun => (computesWithin M hrun).mono ?_ ?_⟩ <;>
    simp only [TimeSpaceModel.sizeCostTree_inputSize, TimeSpaceModel.stack_inputSize,
      RawWord.length_treeEncoding, spaceBound, le_refl]
  exact timeBound_le x.size_pos

/-- Simulation consumes an `O` specification and retains its real input-loading overhead,
bounded by the space budget. Tree codes have positive size, which absorbs the simulator's
fixed setup cost. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableIn.toStack_of_tree
    {f : α → β} {t s : α → ℕ}
    (h : TimeSpaceModel.sizeCostTree.ComputableIn f IsO(t) IsO(s)) :
    TimeSpaceModel.stack.ComputableIn f IsO(fun a => t a + s a) IsO(s) := by
  classical
  obtain ⟨u, v, h, hu, hv⟩ := h
  obtain ⟨k, hk, Q, hQ, M, h⟩ := computableWithin_iff.mp h
  have hpos (a : α) : 0 < v a := by
    obtain ⟨r, hr⟩ := e.exists_code a
    obtain ⟨_, _, hrun⟩ := h a r hr
    exact r.size_pos.trans_le hrun.input_size_le_space
  let : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  exact ⟨_, _, h.toStack.computableWithin,
    (Dominated.of_le_mul _ fun a => timeBound_le (hpos a)).trans (hu.add hv),
    hv.const_mul_left _⟩

end InputBudgets

end Complexity.TreeMachine
