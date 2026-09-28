/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeFunctions
public import Complexity.Resources.TreeMachine.Composition
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Fin

/-! # Composition of polynomial-time tree computations -/

@[expose] public section

namespace Complexity.TreeFP

variable {α β γ : Type*} [Encoding Tree α] [Encoding Tree β] [Encoding Tree γ]
  {f : α → β} {g : β → γ}

private theorem exists_polynomial_bound (h : f ∈ TreeFP) :
    ∃ p : Polynomial ℕ, TreeMachine.ComputableInTime f p.eval := by
  obtain ⟨d, t, h, ht⟩ := mem_iff_exists_ftime.mp h
  obtain ⟨p, hp⟩ := ht.exists_polynomial_bound
  exact ⟨p, h.mono hp⟩

/-- Polynomial-time tree computations are closed under composition, even when
valid codes are not unique. -/
theorem comp (hg : g ∈ TreeFP) (hf : f ∈ TreeFP) : g ∘ f ∈ TreeFP := by
  obtain ⟨p, s, k, hk, Q, hQ, M, hf⟩ := exists_polynomial_bound hf
  obtain ⟨q, v, l, hl, Q', hQ', N, hg⟩ := exists_polynomial_bound hg
  let a : Polynomial ℕ := Polynomial.X + Polynomial.C k + p
  let b : Polynomial ℕ := p + Polynomial.C (max k l) + q.comp a
  have h := hg.comp hf q.monotone_eval_nat
  obtain ⟨d, hb⟩ := IsBigO.exists_pow b
  apply ftime_subset d
  refine ⟨b.eval, ⟨_, h.computableInTimeAndSpace.mono ?_ (fun _ => le_rfl)⟩, hb⟩
  intro n
  simp [TreeMachine.compTimeBound, b, a]

private def identity : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| .keep ()

/-- Leaving the input register unchanged computes the identity at zero time cost. -/
theorem id : (id : α → α) ∈ TreeFP := by
  apply of_time_le (t := fun _ => 0) (c := 0) (d := 0) _ (by simp)
  refine ⟨fun n => n, 1, inferInstance, Unit, inferInstance, identity, ?_⟩
  intro a x hx
  refine ⟨a, hx, 0, rfl, ?_, ?_, ?_⟩
  · exact TreeMachine.input_get (0 : Fin 1) a
  · simp
  · simp [TreeMachine.Cfg.mass]

end Complexity.TreeFP
