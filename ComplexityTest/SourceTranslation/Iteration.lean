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
example (f : Bool → Bool) {qf : Value → Code Value} {t p : Bool → ℕ} (hf : HasProgram f qf t p) :=
  (by source_fun_prop : type_of% hf.iterate)

-- The growth refers to the chosen callback's growth at each visited state.
example (f : Bool → Bool) {qf : Value → Code Value} {t p : Bool → ℕ} (_hf : HasProgram f qf t p) :
    HasProgram (fun x : ℕ × Bool => f^[x.1] x.2) hole(qf ⊢ program)
      (fun x => iterateTime f t x.1 x.2 + 1) (fun x => iteratePeak f p x.1 x.2) := by
  fill_hole program in source_fun_prop

def repeatReverse (x : ℕ × List Bool) := List.reverse^[x.1] x.2
example := (by source_fun_prop : HasProgram repeatReverse _ _ _)

def repeatAnd (x : List Unit × Bool × Bool) :=
  (fun a => x.2.1 && a)^[x.1.length] x.2.2
example := (by source_fun_prop : HasProgram repeatAnd _ _ _)

def repeatNot (x : List Unit × Bool) := Bool.not^[x.1.length] x.2
example := (by source_fun_prop : HasProgram repeatNot _ _ _)

section Captured

variable (f : Bool → Bool → Bool) (count : Bool → ℕ) (initial : Bool → Bool)

example {qi qs : Value → Code Value} {ti pi : Bool → ℕ} {ts ps : Bool × Bool → ℕ}
    (hi : HasProgram (fun e => (count e, (e, initial e))) qi ti pi)
    (hs : HasProgram (fun x : Bool × Bool => f x.1 x.2) qs ts ps) :=
  (by source_fun_prop : type_of% (hi.iterateWith hs))

end Captured

-- Separate implementations for each environment are not a uniform callback.
example (f : Bool → Bool → Bool) (program : Bool → Value → Code Value)
    (_h : ∀ e, HasProgram (f e) (program e) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by source_fun_prop :
      HasProgram (fun x : ℕ × Bool × Bool => (f x.2.1)^[x.1] x.2.2) _ _ _)
  trivial

-- Two iterations pay both state-dependent callbacks once, and each binary counter step.
example (f : Bool → Bool) (t : Bool → ℕ) (a : Bool) :
    iterateTime f t 2 a = t a + t (f a) + ⌜(2 : ℕ)⌝ₜ.size + ⌜(1 : ℕ)⌝ₜ.size := by
  simp only [iterateTime_succ, iterateTime_zero, Nat.reduceAdd]
  omega

-- A varying round allowance retains the sum of the two visited callback growths.
-- The proof uses a potential and the source invariant.
example {α : Type*} [UniqueEncoding Tree α] {f : α → α} {t p : α → ℕ} :
    Dominated (fun x => iterateTime f t 2 x) (fun x => t x + t (f x) + 1) := by
  let I (x : α) (n : ℕ) (a : α) :=
    (n = 2 ∧ a = x) ∨ (n = 1 ∧ a = f x) ∨ (n = 0 ∧ a = f (f x))
  let remaining (_ : α) (n : ℕ) (a : α) :=
    if n = 0 then 0 else if n = 1 then t a + ⌜(1 : ℕ)⌝ₜ.size
    else (t a + ⌜(2 : ℕ)⌝ₜ.size) + (t (f a) + ⌜(1 : ℕ)⌝ₜ.size)
  let peak (x : α) :=
    max (max ⌜((2 : ℕ), x)⌝ₜ.size
      (max ⌜((1 : ℕ), f x)⌝ₜ.size ⌜((0 : ℕ), f (f x))⌝ₜ.size))
      (max (p x) (p (f x)))
  have bounds := Dominated.iterate_of_potential (f := f) (t := t) (p := p) I (fun _ => 2) id
    remaining peak (fun _ => Or.inl ⟨rfl, rfl⟩) (fun x n a hi => by
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
    (Dominated.const (⌜(2 : ℕ)⌝ₜ.size + ⌜(1 : ℕ)⌝ₜ.size))).mono_left
  intro x
  norm_num only [remaining, id_eq]
  simp only [ite_false]
  omega

-- Zero captured iterations charge preparation once; no callback growth remains.
example {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {initial : ρ → α} {qi qs : Value → Code Value} {ti pi : ρ → ℕ}
    {t p : ρ × α → ℕ} (hi : HasProgram (fun e => ((0 : ℕ), (e, initial e))) qi ti pi)
    (hs : HasProgram (fun x : ρ × α => f x.1 x.2) qs t p) :
    HasProgram (fun e => (f e)^[0] (initial e)) hole(qi, qs ⊢ program) (fun e => ti e + 1)
      (fun e => max (pi e) (⌜e⌝ₜ.size + 1 + ⌜((0 : ℕ), initial e)⌝ₜ.size)) := by
  fill_hole program in
    exact (hi.iterateWith hs).mono (Dominated.of_le fun _ => by simp)
      (Dominated.of_le fun _ => by simp)

end ComplexityTest.SourceTranslation.Iteration
