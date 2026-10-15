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

variable {α β : Type*} [e : Encoding Tree α] [d : Encoding Tree β]

/-- Serialization keeps budgets indexed by the source input. Loading still costs the
actual tree size, even when the chosen time budget is zero. -/
theorem Computes.toStack {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]
    {M : TreeMachine Id k Q} {f : α → β} {t s : α → ℕ} (h : Computes M f t s)
    (sizeBound : α → ℕ) (hsize : ∀ (r : Tree) a, a ∈ decode α r → r.size ≤ sizeBound a) :
    StackMachine.Computes (compiler M) f
      (fun a => timeBound k (sizeBound a) (t a)) (fun a => spaceBound k (s a)) := by
  intro a xs ha
  obtain ⟨x, hx, hax⟩ := (Encoding.mem_comp_iff RawWord.treeEncoding.toEncoding e).mp ha
  obtain rfl := RawWord.treeEncoding.mem_decode_iff.mp hx
  obtain ⟨y, hy, hrun⟩ := h a x hax
  refine ⟨RawWord.treeEncoding.encode y,
    (Encoding.mem_comp_encode RawWord.treeEncoding d).mpr hy, ?_⟩
  have hc := computesWithin M hrun
  have ht : timeBound k x.size (t a) ≤ timeBound k (sizeBound a) (t a) := by
    have hs := hsize x a hax
    simp only [timeBound]
    omega
  exact hc.mono ht le_rfl

/-- Simulation consumes a growth specification and retains its real input-loading overhead.
Tree codes have positive size, which absorbs the simulator's fixed setup cost. -/
theorem _root_.Complexity.TimeSpaceModel.ComputableWithGrowth.toStack_of_tree
    {f : α → β} {t s : α → ℕ}
    (h : TimeSpaceModel.sizeCostTree.ComputableWithGrowth f t s)
    (sizeBound : α → ℕ) (hsize : ∀ (r : Tree) a, a ∈ decode α r → r.size ≤ sizeBound a) :
    TimeSpaceModel.stack.ComputableWithGrowth f
      (fun a => t a + sizeBound a) s := by
  classical
  have hpos (a : α) : 0 < sizeBound a := by
    obtain ⟨r, hr⟩ := e.exists_code a
    exact (Tree.size_pos r).trans_le (hsize r a hr)
  obtain ⟨u, v, h, hu, hv⟩ := h
  obtain ⟨k, hk, Q, hQ, M, h⟩ := computableWithin_iff.mp h
  let : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  refine ⟨_, _, (h.toStack sizeBound hsize).computableWithin, ?_, ?_⟩
  · have hsize : Dominated (fun a : α => sizeBound a)
        (fun a => t a + sizeBound a) :=
      Dominated.of_le fun _ => Nat.le_add_left _ _
    have htime := hu.mono (fun a => Nat.le_add_right (t a) (sizeBound a))
    have hconst : Dominated (fun _ : α => 6 * k + 8)
        (fun a => t a + sizeBound a) :=
      (Dominated.of_le_mul (6 * k + 8) fun a =>
        Nat.le_mul_of_pos_right _ (hpos a)).trans hsize
    convert ((htime.const_mul_left 43).add_same (hsize.const_mul_left 12)).add_same hconst
      using 1
    funext a
    simp only [timeBound]
    omega
  · exact hv.const_mul_left _

end InputBudgets

end Complexity.TreeMachine
