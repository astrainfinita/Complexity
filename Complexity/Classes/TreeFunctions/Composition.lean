/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Reductions.Basic
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
  obtain ⟨p, s, R, ⟨k, hk, Q, hQ, M, rfl⟩, hf⟩ := FP.exists_polynomial_bound hf
  obtain ⟨q, v, R', ⟨l, hl, Q', hQ', N, rfl⟩, hg⟩ := FP.exists_polynomial_bound hg
  let a : Polynomial ℕ := Polynomial.X + Polynomial.C k + p
  let b : Polynomial ℕ := p + Polynomial.C (max k l) + q.comp a
  obtain ⟨d, hb⟩ := Polynomial.exists_dominatedAtTop_pow b
  apply FP.ftime_subset d
  refine ⟨b.eval, ⟨fun n => n + (max k l + 1) + b.eval n, _,
    ⟨max k l + 1, inferInstance, _, inferInstance, M.comp N, rfl⟩, ?_⟩, hb⟩
  intro x r hx
  obtain ⟨y, hy, hm⟩ := hf x r hx
  obtain ⟨z, hz, hn⟩ := hg (f x) y hy
  have ht : p.eval r.size + max k l + q.eval y.size ≤ b.eval r.size := by
    have hy := q.monotone_eval_nat hm.output_size_le
    simp only [b, a, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_X]
    exact Nat.add_le_add_left hy _
  have hcomp := comp_computesWithin M N hm hn
  exact ⟨z, hz, hcomp.space_of_time.mono ht (Nat.add_le_add_left ht _)⟩

private def identity : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| .keep ()

/-- Leaving the input register unchanged computes the identity at zero time cost. -/
theorem fp_id : (id : α → α) ∈ FP .sizeCostTree := by
  apply FP.of_time_le (t := fun _ => 0) _ 0 0 (by simp)
  refine ⟨fun _ => 0, ⟨fun n => n, _,
    ⟨1, inferInstance, Unit, inferInstance, identity, rfl⟩, ?_⟩, DominatedAtTop.refl _⟩
  intro x a hx
  refine ⟨a, hx, 0, rfl, ?_, ?_, ?_⟩
  · exact TreeMachine.input_get (0 : Fin 1) a
  · simp
  · simp [TreeMachine.Cfg.mass, TimeSpaceModel.sizeCostTree]

end Complexity.TreeMachine

namespace Complexity.PolytimeManyOneReducible

variable {α β γ : Type*} [Encoding Tree α] [Encoding Tree β] [Encoding Tree γ]

theorem refl (p : α → Prop) : PolytimeManyOneReducible .sizeCostTree p p :=
  ⟨id, TreeMachine.fp_id, fun _ => Iff.rfl⟩

theorem trans {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    (hpq : PolytimeManyOneReducible .sizeCostTree p q)
    (hqr : PolytimeManyOneReducible .sizeCostTree q r) :
    PolytimeManyOneReducible .sizeCostTree p r := by
  obtain ⟨f, hf, hp⟩ := hpq
  obtain ⟨g, hg, hq⟩ := hqr
  exact ⟨g ∘ f, TreeMachine.fp_comp hg hf, fun x => (hp x).trans (hq (f x))⟩

end Complexity.PolytimeManyOneReducible
