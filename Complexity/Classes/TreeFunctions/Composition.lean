/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic
public import Complexity.Resources.TreeMachine.Composition
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Fin

/-! # Composition of polynomial-time tree computations -/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β γ : Type*} [Encoding Tree α] [Encoding Tree β] [Encoding Tree γ]
  {f : α → β} {g : β → γ}

/-- Polynomial-time tree computations are closed under composition, even when
valid codes are not unique. -/
theorem fp_comp (hg : g ∈ FP .sizeCostTree) (hf : f ∈ FP .sizeCostTree) :
    g ∘ f ∈ FP .sizeCostTree := by
  obtain ⟨p, s, -, hp, R, ⟨k, hk, Q, hQ, M, rfl⟩, hf⟩ := FP.exists_monotone_isPoly hf
  obtain ⟨q, v, hmono, hq, R', ⟨l, hl, Q', hQ', N, rfl⟩, hg⟩ := FP.exists_monotone_isPoly hg
  let b (n : ℕ) : ℕ := p n + max k l + q (n + k + p n)
  have hb : IsPoly (fun n => n) b := (hp.add (.const _)).add
    (hq.comp (h := fun n => n + k + p n) ((IsPoly.refl.add (.const k)).add hp))
  refine FP.mem_iff_isPoly.2 ⟨b, fun n => n + (max k l + 1) + b n,
    ⟨_, ⟨max k l + 1, inferInstance, _, inferInstance, M.comp N, rfl⟩, ?_⟩, hb⟩
  intro x r hx
  obtain ⟨y, hy, hm⟩ := hf x r hx
  obtain ⟨z, hz, hn⟩ := hg (f x) y hy
  have ht : p r.size + max k l + q y.size ≤ b r.size :=
    Nat.add_le_add_left (hmono hm.output_size_le) _
  have hcomp := comp_computesWithin M N hm hn
  exact ⟨z, hz, hcomp.space_of_time.mono ht (Nat.add_le_add_left ht _)⟩

private def identity : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure ((), .nop)

/-- Leaving the input register unchanged computes the identity at zero time cost. -/
theorem fp_id : (id : α → α) ∈ FP .sizeCostTree := by
  refine FP.mem_iff_isPoly.2 ⟨fun _ => 0, fun n => n,
    ⟨_, ⟨1, inferInstance, Unit, inferInstance, identity, rfl⟩, ?_⟩, .const 0⟩
  intro x a hx
  refine ⟨a, hx, .of_halted 0 rfl ?_ ?_ ?_⟩
  · exact TreeMachine.input_get (0 : Fin 1) a
  · simp
  · simp [TreeMachine.Cfg.mass]

end Complexity.TreeMachine
