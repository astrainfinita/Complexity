/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Iteration

-- The loop stores executable code and keeps the selected callback.
example (f : Bool → Bool) (hf : Implementation f) :
    (show Implementation (fun x : ℕ × Bool => f^[x.1] x.2) from by source_fun_prop).program =
      hf.iterate.program := rfl

def repeatReverse (x : ℕ × List Bool) := List.reverse^[x.1] x.2
example : Implementation repeatReverse := by source_fun_prop

def repeatAnd (x : List Unit × Bool × Bool) :=
  (fun a => x.2.1 && a)^[x.1.length] x.2.2
example : Implementation repeatAnd := by source_fun_prop

-- The bounds continue to refer to the chosen callback's evaluation at each visited state.
example (f : Bool → Bool) (hf : Implementation f) :
    hf.iterate.bounds = iterateBounds f hf.bounds := Implementation.bounds_iterate hf

section Captured

variable (f : Bool → Bool → Bool) (count : Bool → ℕ) (initial : Bool → Bool)

example (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : Bool × Bool => f x.1 x.2)) :
    (show Implementation (fun e => (f e)^[count e] (initial e)) from by source_fun_prop).program =
      (hi.iterateWith hs).program := rfl

example (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : Bool × Bool => f x.1 x.2)) :
    (hi.iterateWith hs).bounds = iterateWithBounds f count initial hi.bounds hs.bounds := by simp

end Captured

-- Separate implementations for each environment are not a uniform callback.
example (f : Bool → Bool → Bool) (_h : ∀ e, Implementation (f e)) : True := by
  fail_if_success
    have : Implementation (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) := by
      source_fun_prop
  trivial

-- Two iterations pay both state-dependent callbacks once; controller time is independent
-- of the callback's resource specification.
example (f : Bool → Bool) (hf : Implementation f) (a : Bool) :
    hf.iterate.bounds.time (2, a) = hf.bounds.time a + hf.bounds.time (f a) +
      (Implementation.identity (α := Bool)).iterate.bounds.time (2, a) := by
  simp [iterateBounds]
  omega

def repeatNot (x : List Unit × Bool) := Bool.not^[x.1.length] x.2
example : Implementation repeatNot := by source_fun_prop

-- A varying round allowance retains the sum of the two visited callback specifications.
-- The proof uses a potential and the source invariant, without inspecting callback budgets.
example {α : Type*} [UniqueEncoding Tree α] {f : α → α} {hf : Implementation f}
    {t p : α → ℕ} (h : hf.HasGrowth t p) :
    Dominated (fun x => hf.iterate.bounds.time (2, x)) (fun x => t x + t (f x) + 1) := by
  let I (x : α) (n : ℕ) (a : α) :=
    (n = 2 ∧ a = x) ∨ (n = 1 ∧ a = f x) ∨ (n = 0 ∧ a = f (f x))
  let remaining (_ : α) (n : ℕ) (a : α) :=
    if n = 0 then 0 else if n = 1 then t a + ⌜(1 : ℕ)⌝ₜ.size + 1
    else (t a + ⌜(2 : ℕ)⌝ₜ.size + 1) + (t (f a) + ⌜(1 : ℕ)⌝ₜ.size + 1)
  let peak (x : α) :=
    max (max ⌜((2 : ℕ), x)⌝ₜ.size
      (max ⌜((1 : ℕ), f x)⌝ₜ.size ⌜((0 : ℕ), f (f x))⌝ₜ.size))
      (max (p x) (p (f x)))
  have bounds := h.iterate_of_potential I (fun _ => 2) id remaining peak
    (fun _ => Or.inl ⟨rfl, rfl⟩) (fun x n a hi => by
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
      · omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · have : n = 1 := by omega
        subst n
        simp [remaining]
      · have : n = 0 := by omega
        subst n
        simp [remaining]
      · omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp [peak] <;> omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨x, n, a⟩, hi⟩
      dsimp only [I] at hi ⊢
      rcases hi with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, _⟩
      · dsimp [peak]
        omega
      · dsimp [peak]
        omega
      · omega)
  apply bounds.1.trans
  apply (((Dominated.refl t).add (Dominated.refl (fun x => t (f x)))).add
    (Dominated.const (⌜(2 : ℕ)⌝ₜ.size + ⌜(1 : ℕ)⌝ₜ.size + 3))).mono_left
  intro x
  norm_num only [remaining, id_eq]
  simp only [ite_false]
  omega

-- Zero captured iterations retain one selected implementation and charge preparation once.
-- No callback time or peak allowance appears in the resulting specification.
example {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {initial : ρ → α}
    {hi : Implementation (fun e => ((0 : ℕ), (e, initial e)))}
    {hs : Implementation (fun x : ρ × α => f x.1 x.2)}
    {ti pi : ρ → ℕ} {t p : ρ × α → ℕ}
    (prep : hi.HasGrowth ti pi) (step : hs.HasGrowth t p) :
    (hi.iterateWith hs).HasGrowth (fun e => ti e + 1)
      (fun e => max (pi e) ⌜((0 : ℕ), (e, initial e))⌝ₜ.size) := by
  simpa only [Nat.zero_mul, Nat.zero_add] using prep.iterateWith step
    (fun e n a => n = 0 ∧ a = initial e) (fun _ => 1)
    (fun e => ⌜((0 : ℕ), (e, initial e))⌝ₜ.size)
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ h => by omega)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨e, n, a⟩, hn, ha⟩
      dsimp only at hn ha ⊢
      subst n a
      simp)
    (Dominated.of_le fun z => by
      rcases z with ⟨⟨e, n, a⟩, hn, ha⟩
      dsimp only at hn ha ⊢
      subst n a
      exact Nat.le_refl _)
    (Dominated.of_le fun z => by
      have hn := z.2.1
      omega)
    (Dominated.of_le fun z => by
      have hn := z.2.1
      omega)

end ComplexityTest.SourceTranslation.Iteration
