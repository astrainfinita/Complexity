/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine.Basic
public import Complexity.Resources.StackMachine.Basic
public import Complexity.Models.TreeMachine.Simulation.Correctness

/-! # Serialized tree computations on stack machines -/

@[expose] public section

namespace Complexity.TreeMachine

open Simulation

/-- Serializing tree codes transports every valid input and output, with the
simulator's linear time and space bounds. No per-type encoding conversion is needed. -/
theorem Computes.toStack {α β : Type*} [e : Encoding Tree α] [d : Encoding Tree β]
    {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q] {M : TreeMachine Id k Q}
    {f : α → β} {t s : ℕ → ℕ} (h : Computes M f t s) :
    StackMachine.Computes (compiler M) f
      (fun n ↦ timeBound k n (t n)) (fun n ↦ spaceBound k (s n)) := by
  intro xs a ha
  obtain ⟨x, hx, hax⟩ := (Encoding.mem_comp_iff RawWord.treeEncoding.toEncoding e).mp ha
  obtain rfl := RawWord.treeEncoding.mem_decode_iff.mp hx
  obtain ⟨y, hy, hrun⟩ := h x a hax
  refine ⟨RawWord.treeEncoding.encode y,
    (Encoding.mem_comp_encode RawWord.treeEncoding d).mpr hy, ?_⟩
  simpa [RawWord.treeEncoding_encode] using computesInTimeAndSpace M hrun

end Complexity.TreeMachine
