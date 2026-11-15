/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine.Basic
public import Complexity.Models.TreeMachine.Composition

/-! # Composition of encoded tree computations

Both machines receive value-indexed budgets on every valid code. Composition
therefore uses the second budget at the intermediate value, without imposing
monotonicity or choosing an intermediate representation. Peak space is the larger
of the two phase budgets after padding their register files.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {α β γ : Type*} [Encoding Tree α] [Encoding Tree β] [Encoding Tree γ]
  {k l : ℕ} [NeZero k] [NeZero l] {Q Q' : Type}

/-- Compose computations on all valid codes, allowing any valid intermediate
representation of the computed value. The clearing pass costs a fixed number of
instructions, and the two phases share their work registers. -/
theorem Computes.comp {M : TreeMachine Id k Q} {N : TreeMachine Id l Q'}
    {f : α → β} {g : β → γ} {t s : α → ℕ} {u v : β → ℕ}
    (hg : Computes N g u v) (hf : Computes M f t s) :
    Computes (M.comp N) (g ∘ f)
      (fun x => t x + max k l + u (f x))
      (fun x => max (s x + (max k l + 1 - k)) (v (f x) + (max k l + 1 - l))) := by
  intro a src hsrc
  obtain ⟨mid, hmid, hm⟩ := hf a src hsrc
  obtain ⟨dst, hdst, hn⟩ := hg (f a) mid hmid
  exact ⟨dst, hdst, comp_computesWithin M N hm hn⟩

/-- Compose `O` specifications on every input of two fixed machines. The clearing pass and
register padding remain in the bound, including when either component has zero
time. All valid codes of an intermediate value share its resource specification. -/
theorem comp_computesInO {M : TreeMachine Id k Q} {N : TreeMachine Id l Q'}
    {f : α → β} {g : β → γ} {T S : α → ℕ} {U V : β → ℕ}
    (hg : ∃ u v, Computes N g u v ∧ Dominated u U ∧ Dominated v V)
    (hf : ∃ t s, Computes M f t s ∧ Dominated t T ∧ Dominated s S) :
    ∃ t s, Computes (M.comp N) (g ∘ f) t s ∧
      Dominated t (fun x => T x + max k l + U (f x)) ∧
      Dominated s
        (fun x => max (S x + (max k l + 1 - k)) (V (f x) + (max k l + 1 - l))) := by
  obtain ⟨u, v, hg, hu, hv⟩ := hg
  obtain ⟨t, s, hf, ht, hs⟩ := hf
  exact ⟨_, _, hg.comp hf,
    (ht.add (Dominated.refl _)).add (hu.comp f),
    (hs.add (Dominated.refl _)).max ((hv.comp f).add (Dominated.refl _))⟩

end Complexity.TreeMachine
